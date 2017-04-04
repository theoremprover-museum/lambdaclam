;; proof-script.el  Major mode for proof assistant script files.
;;
;; Copyright (C) 1994-2001 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; proof-script.el,v 5.11 2001/08/10 15:01:21 da Exp
;;

(require 'proof)			; loader
(require 'proof-syntax)			; utils for manipulating syntax
(require 'span)				; abstraction of overlays/extents
(require 'pg-user)			; user-level commands
(require 'proof-menu)			; menus for script mode



;; Nuke some byte-compiler warnings 
;; NB: eval-when (compile) is different to eval-when-compile!!
(eval-when (compile)
  (proof-try-require 'func-menu)
  (require 'comint))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  Internal variables used by script mode
;;

(deflocal proof-active-buffer-fake-minor-mode nil
  "An indication in the modeline that this is the *active* script buffer")

(defvar proof-last-theorem-dependencies nil
  "Contains the dependencies of the last theorem 
Set in proof-shell-process-urgent-message.")

;; FIXME da: is this Isabelle specific?
(defvar thy-mode-deps-menu nil
  "Contains the dependence menu for thy mode")

(defvar proof-thm-names-of-files nil
  "Names of files.
A list of lists; the first element of each list is a file-name, the
second element a list of all the thm names in that file")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Configuration of function-menu (aka "fume")	
;;
;; FIXME: we would like this code only enabled if the user loads
;; func-menu into Emacs.
;;

(deflocal proof-script-last-entity nil
  "Record of last entity found.   
A hack for entities that are named in two places, so that find-next-entity 
doesn't return the same values twice.")

;; FIXME mmw: maybe handle comments/strings by using
;; proof-looking-at-syntactic-context 
(defun proof-script-find-next-entity (buffer)
  "Find the next entity for function menu in a proof script.
A value for fume-find-function-name-method-alist for proof scripts.
Uses fume-function-name-regexp, which is intialised from 
proof-script-next-entity-regexps, which see."
  ;; Hopefully this function is fast enough.
  (set-buffer buffer)
  ;;  could as well use next-entity-regexps directly since this is
  ;;  not really meant to be used as a general function. 
  (let ((anyentity	(car fume-function-name-regexp)))
    (if (proof-re-search-forward anyentity nil t)
	;; We've found some interesting entity, but have to find out
	;; which one, and where it begins.  
	(let ((entity (buffer-substring (match-beginning 0) (match-end 0)))
	      (start (match-beginning 0))
	      (discriminators (cdr fume-function-name-regexp))
	      (p (point))
	      disc res)
	  (while (and (not res) (setq disc (car-safe discriminators)))
	    (if (proof-string-match (car disc) entity)
		(let*
		    ((items (nth 1 disc))
		     (items (if (numberp items) (list items) items))
		     (name ""))
		  (dolist (item items)
		    (setq name
			  (concat name
				  (substring entity
					     (match-beginning item)
					     (match-end item))
				  " ")))
		  (cond
		   ((eq (nth 2 disc) 'backward)
		    (setq start
			  (or (proof-re-search-backward (nth 3 disc) nil t)
			      start))
		    (goto-char p))
		   ((eq (nth 2 disc) 'forward)
		    (proof-re-search-forward (nth 3 disc))))
		  (setq res (cons name start)))
	      (setq discriminators (cdr discriminators))))
	  res))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic code for the locked region and the queue region            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; da FIXME: clean this section

;; Notes on markup in the scripting buffer. (da)
;;
;; The locked region is covered by a collection of non-overlaping
;; spans (our abstraction of extents/overlays).
;;
;; For an unfinished proof, there is one extent for each command 
;; or comment outside a command.   For a finished proof, there
;; is one extent for the whole proof.
;;
;; Each command span has a 'type property, one of:
;;
;;     'proof	     A goal..savegoal region in the buffer, a completed proof.
;;     'vanilla      Initialised in proof-semis-to-vanillas, for
;;     'comment      A comment outside a command.
;;     'proverproc   A region closed by the prover, processed outwith PG
;;     'pbp	     A PBP command inserted automatically into the script
;;
;;  All spans except those of type 'comment have a 'cmd property,
;;  which is set to a string of its command.  This is the
;;  text in the buffer stripped of leading whitespace and any comments.
;;
;; 



(deflocal proof-locked-span nil
  "The locked span of the buffer.
Each script buffer has its own locked span, which may be detached
from the buffer.
Proof General allows buffers in other modes also to be locked;
these also have a non-nil value for this variable.")

;; da: really we only need one queue span rather than one per buffer,
;; but I've made it local because the initialisation occurs in
;; proof-init-segmentation, which can happen when a file is visited.
;; So nasty things might happen if a locked file is visited whilst
;; another buffer has a non-empty queue region being processed.

(deflocal proof-queue-span nil
  "The queue span of the buffer.  May be detached if inactive or empty.")

;; FIXME da: really the queue region should always be locked strictly.

(defun proof-span-read-only (span)
  "Make span be read-only, if proof-strict-read-only is non-nil.
Otherwise make span give a warning message on edits."
  (if proof-strict-read-only
      (span-read-only span)
    (span-write-warning span)))

;; not implemented yet; toggle via restarting scripting
;; (defun proof-toggle-strict-read-only ()
;;  "Toggle proof-strict-read-only, changing current spans."
;;  (interactive)
;;   map-spans blah
;;  )

(defun proof-init-segmentation ()
  "Initialise the queue and locked spans in a proof script buffer.
Allocate spans if need be.  The spans are detached from the
buffer, so the regions are made empty by this function."
  ;; Initialise queue span, remove it from buffer.
  (unless proof-queue-span
      (setq proof-queue-span (make-span 1 1))
      ;; FIXME: span-raise is an FSF hack to make locked span appear.
      ;; overlays still don't work as well as they did/should.
      (span-raise proof-queue-span))
  (set-span-property proof-queue-span 'start-closed t)
  (set-span-property proof-queue-span 'end-open t)
  (proof-span-read-only proof-queue-span)
  (set-span-property proof-queue-span 'face 'proof-queue-face)
  (detach-span proof-queue-span)
  ;; Initialise locked span, remove it from buffer
  (unless proof-locked-span
      (setq proof-locked-span (make-span 1 1))
      (span-raise proof-locked-span))
  (set-span-property proof-locked-span 'start-closed t)
  (set-span-property proof-locked-span 'end-open t)
  (proof-span-read-only proof-locked-span)
  (set-span-property proof-locked-span 'face 'proof-locked-face)
  (detach-span proof-locked-span)
  (setq proof-last-theorem-dependencies nil))

;; These two functions are used in coq.el to edit the locked region
;; (by lifting local (nested) lemmas out of a proof, to make them global).   
(defsubst proof-unlock-locked ()
  "Make the locked region writable.  
Used in lisp programs for temporary editing of the locked region.
See proof-lock-unlocked for the reverse operation."
  (span-read-write proof-locked-span))

(defsubst proof-lock-unlocked ()
  "Make the locked region read only (according to proof-strict-read-only).
Used in lisp programs for temporary editing of the locked region.
See proof-unlock-locked for the reverse operation."
  (proof-span-read-only proof-locked-span))

(defsubst proof-set-queue-endpoints (start end)
  "Set the queue span to be START, END."
  (set-span-endpoints proof-queue-span start end))

(defsubst proof-set-locked-endpoints (start end)
  "Set the locked span to be START, END."
  (set-span-endpoints proof-locked-span start end))

(defsubst proof-detach-queue ()
  "Remove the span for the queue region."
  (and proof-queue-span (detach-span proof-queue-span)))

(defsubst proof-detach-locked ()
  "Remove the span for the locked region."
  (and proof-locked-span (detach-span proof-locked-span)))

(defsubst proof-set-queue-start (start)
  "Set the queue span to begin at START."
  (set-span-start proof-queue-span start))

;; FIXME da: optional arg here was ignored, have fixed.
;; Do we really need it though?
(defun proof-detach-segments (&optional buffer)
  "Remove locked and queue region from BUFFER.
Defaults to current buffer when BUFFER is nil."
  (let ((buffer (or buffer (current-buffer))))
    (with-current-buffer buffer
      (proof-detach-queue)
      (proof-detach-locked))))

(defsubst proof-set-locked-end (end)
  "Set the end of the locked region to be END.
If END is at or before (point-min), remove the locked region.
Otherwise set the locked region to be from (point-min) to END."
  (if (>= (point-min) end)
      (proof-detach-locked)
    (set-span-endpoints proof-locked-span (point-min) end)
    ;; FIXME: the next line doesn't fix the disappearing regions
    ;; (was span property is lost in latest FSF Emacs, maybe?)
    ;; (set-span-property proof-locked-span 'face 'proof-locked-face)
    ))

;; Reimplemented this to mirror above because of remaining
;; span problen
(defsubst proof-set-queue-end (end)
  "Set the queue span to end at END."
  (if (or (>= (point-min) end)
	  (<= end (span-start proof-queue-span)))
      (proof-detach-queue)
    (set-span-end proof-queue-span end)))


;; FIXME: get rid of this function.  Some places expect this
;; to return nil if locked region is empty.	Moreover,
;; it confusingly returns the point past the end of the 
;; locked region.
(defun proof-locked-end ()
  "Return end of the locked region of the current buffer.
Only call this from a scripting buffer."
  (proof-unprocessed-begin))
  

(defsubst proof-end-of-queue ()
  "Return the end of the queue region, or nil if none."
  (and proof-queue-span (span-end proof-queue-span)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Buffer position functions
;;
;; da:cleaned

(defun proof-unprocessed-begin ()
  "Return end of locked region in current buffer or (point-min) otherwise.
The position is actually one beyond the last locked character."
  (or 
   (and proof-locked-span 
	(span-end proof-locked-span))
   (point-min)))

(defun proof-script-end ()
  "Return the character beyond the last non-whitespace character.
This is the same position proof-locked-end ends up at when asserting
the script.  Works for any kind of buffer."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n")
    (point)))

(defun proof-queue-or-locked-end ()
  "Return the end of the queue region, or locked region, or (point-min).
This position should be the first writable position in the buffer.
An appropriate point to move point to (or make sure is displayed)
when a queue of commands is being processed."
  (or	
   ;; span-end returns nil if span is detatched
   (and proof-queue-span (span-end proof-queue-span))
   (and proof-locked-span (span-end proof-locked-span))
   (point-min)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Predicates for locked region.  
;;
;; These work on any buffer, so that non-script buffers can be locked
;; (as processed files) too.
;;
;; da:cleaned

(defun proof-locked-region-full-p ()
  "Non-nil if the locked region covers all the buffer's non-whitespace.
Works on any buffer."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n")
    (>= (proof-unprocessed-begin) (point))))

(defun proof-locked-region-empty-p ()
  "Non-nil if the locked region is empty.  Works on any buffer."
  (eq (proof-unprocessed-begin) (point-min)))

(defun proof-only-whitespace-to-locked-region-p ()
  "Non-nil if only whitespace separates char after point from end of locked region.
Point should be after the locked region.
NB: If nil, point is left at first non-whitespace character found.
If non-nil, point is left where it was."
  ;; NB: this function doesn't quite do what you'd expect, but fixing it
  ;; breaks proof-assert-until-point and electric-terminator which
  ;; rely on the side effect.  So careful!
  ;; (unless (eobp)
  ;; (forward-char))
  ;;   (save-excursion  -- no, side effect is expected!
  (not (proof-re-search-backward "\\S-" (proof-unprocessed-begin) t)))

(defun proof-in-locked-region-p ()
  "Non-nil if point is in locked region.  Assumes proof script buffer current."
  (< (point) (proof-unprocessed-begin)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Misc movement functions
;;

(defun proof-goto-end-of-locked (&optional switch)
  "Jump to the end of the locked region, maybe switching to script buffer.
If interactive or SWITCH is non-nil, switch to script buffer first."
  (interactive)
  (proof-with-script-buffer
   (if (and (not (get-buffer-window proof-script-buffer))
	    (or switch (interactive-p)))
       (switch-to-buffer proof-script-buffer)
     (goto-char (proof-unprocessed-begin)))))

; NB: think about this because the movement can happen when the user
; is typing, not very nice!
(defun proof-goto-end-of-locked-if-pos-not-visible-in-window ()
  "If the end of the locked region is not visible, jump to the end of it.
A possible hook function for proof-shell-handle-error-or-interrupt-hook.
Does nothing if there is no active scripting buffer, or if
`proof-follow-mode' is set to 'ignore."
  (interactive)
  (if (and proof-script-buffer
	   (not (eq proof-follow-mode 'ignore)))
      (let ((pos (with-current-buffer proof-script-buffer
		   (proof-locked-end)))
	    (win (get-buffer-window proof-script-buffer t)))
	(unless (and win (pos-visible-in-window-p pos))
	  (proof-goto-end-of-locked t)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Names of proofs (and other elements) in a script
;; 
;; New in PG 3.3
;;
;; Each kind of part ("idiom") in a proof script has its own name space.
;; Visibility within a script is then handled with buffer-invisibility-spec
;; controlling appearance of each idiom.
;;
;; TODO:
;;   -- Use fine-scale and large scale control, after all?
;;   -- Deleting spans must remove their entries in pg-script-portions !!


;; FIXME: this should be a configuration variable
(defvar pg-idioms '(proof)
  "Vector of script element kinds PG is aware of for this prover.")

(deflocal pg-script-portions nil
  "Table of lists of symbols naming script portions which have been processed so far.")

(defun pg-clear-script-portions ()
  (setq pg-script-portions nil))

(defun pg-add-script-element (elt)
  (add-to-list pg-script-portions elt))

(defun pg-remove-script-element (eltname)
  (setq pg-script-portions (remassoc eltname pg-script-portions)))

(defsubst pg-visname (namespace name)
  (intern (concat namespace ":" name)))

(defun pg-add-element (idiom name span)
  (let* ((ns       (intern idiom))
	 (id       (intern name))
	 (visname  (pg-visname idiom name))
	 (elts	   (cdr-safe (assq ns pg-script-portions))))
    (if elts
	(nconc elts (list id))
      (setq pg-script-portions (cons (cons ns (list id)) pg-script-portions)))
    (set-span-property span 'invisible visname)))

(defun pg-remove-element (idiom name)
  (let ((eltname (intern (concat idiom ":" name))))
    (pg-remove-script-element eltname)))

(defun pg-make-element-invisible (idiom name)
  (add-to-list 'buffer-invisibility-spec 
	       (cons (pg-visname idiom name) t)))

(defun pg-make-element-visible (idiom name)
  (setq buffer-invisibility-spec
	(remassq (pg-visname idiom name) buffer-invisibility-spec)))

(defun pg-show-all-portions (idiom &optional hide)
  "Show or hide all portions of kind IDIOM"
  (interactive
   (list 
    (completing-read 
     (concat "Make " (if current-prefix-arg "in" "") "visible all regions of: ")
     (apply 'vector pg-idioms) nil t)
    current-prefix-arg))
  (let ((elts      (cdr-safe (assq (intern idiom) pg-script-portions)))
	(alterfn   (if hide
		       (lambda (arg) (pg-make-element-invisible idiom 
								(symbol-name arg)))
		     (lambda (arg) (pg-make-element-visible idiom 
							    (symbol-name arg))))))
    (mapcar alterfn elts)))

(defun pg-show-all-proofs ()
  (interactive)
  (pg-show-all-portions "proof"))

(defun pg-add-proof-element (name span)
  (pg-add-element "proof" name span)
  (if proof-disappearing-proofs 
      (pg-make-element-invisible "proof" name)))


  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling
;;
;;
;; da:cleaned

(defun proof-complete-buffer-atomic (buffer)
  "Make sure BUFFER is marked as completely processed, completing with a single step.

If buffer already contains a locked region, only the remainder of the
buffer is closed off atomically.

This works for buffers which are not in proof scripting mode too,
to allow other files loaded by proof assistants to be marked read-only." 
;; FIXME: this isn't quite right, because not all of the structure 
;; in the locked region will be preserved when processing across several 
;; files.
;; In particular, the span for a currently open goal should be removed.
;; Keeping the structure is an approximation to make up for the fact
;; that that no structure is created by loading files via the 
;; proof assistant.
;; Future idea: proof assistant could ask Proof General to do the
;; loading, to alleviate file handling there?!
  (save-excursion
    (set-buffer buffer)
    (if (< (proof-unprocessed-begin) (proof-script-end))
	(let ((span (make-span (proof-unprocessed-begin) 
			       (proof-script-end)))
	      cmd)
	  (if (eq proof-buffer-type 'script) 
	      ;; For a script buffer
	      (progn
		(goto-char (point-min))
		(proof-goto-command-end)
		(let ((cmd-list (member-if
				 (lambda (entry) (equal (car entry) 'cmd))
				 (proof-segment-up-to (point)))))
		  ;; Reset queue and locked regions.
		  (proof-init-segmentation)
		  (if cmd-list 
		      (progn
			;; FIXME 3.3 da: this can be simplified now,
			;; we don't need to set cmd for proverproc
			(setq cmd (second (car cmd-list)))
			(set-span-property span 'type 'proverproc)
			(set-span-property span 'cmd cmd))
		    ;; If there was no command in the buffer, atomic span
		    ;; becomes a comment. This isn't quite right because
		    ;; the first ACS in a buffer could also be a goal-save
		    ;; span. We don't worry about this in the current
		    ;; implementation. This case should not happen in a
		    ;; LEGO module (because we assume that the first
		    ;; command is a module declaration). It should have no
		    ;; impact in Isabelle either (because there is no real
		    ;; retraction).
		    (set-span-property span 'type 'comment))))
	    ;; For a non-script buffer
	    (proof-init-segmentation)
	    (set-span-property span 'type 'comment))
	  ;; End of locked region is always end of buffer
	  (proof-set-locked-end (proof-script-end))))))





;; FIXME da: cleanup of odd asymmetry here: we have a nice setting for
;; proof-register-possibly-new-processed-file but something much more
;; complicated for retracting, because we allow a hook function
;; to calculate the new included files list.

(defun proof-register-possibly-new-processed-file (file &optional informprover noquestions)
  "Register a possibly new FILE as having been processed by the prover.

If INFORMPROVER is non-nil, the proof assistant will be told about this,
to co-ordinate with its internal file-management.  (Otherwise we assume
that it is a message from the proof assistant which triggers this call).
In this case, the user will be queried to save some buffers, unless
NOQUESTIONS is non-nil.

No action is taken if the file is already registered.

A warning message is issued if the register request came from the
proof assistant and Emacs has a modified buffer visiting the file."
  (let* ((cfile (file-truename file))
	 (buffer (proof-file-to-buffer cfile)))
    (proof-debug (concat "Registering file " cfile 
			 (if (member cfile proof-included-files-list)
			     " (already registered, no action)." ".")))
    (unless (member cfile proof-included-files-list)
      (and buffer
	   (not informprover)
	   (buffer-modified-p buffer)
	   (proof-warning (concat "Changes to "
				  (buffer-name buffer)
				  " have not been saved!")))
      ;; Add the new file onto the front of the list
      (setq proof-included-files-list
	    (cons cfile proof-included-files-list))
      ;; If the file is loaded into a buffer, make sure it is completely locked
      (if buffer
	  (proof-complete-buffer-atomic buffer))
      ;; Tell the proof assistant, if we should and if we can
      (if (and informprover proof-shell-inform-file-processed-cmd)
	  (progn
	    ;; Markus suggests we should ask if the user wants to save
	    ;; the file now (presumably because the proof assistant
	    ;; might examine the file timestamp, or attempt to visit
	    ;; the file later??).
	    ;; Presumably it would be enough to ask about this file,
	    ;; not all files?
	    (if (and
		 proof-query-file-save-when-activating-scripting
		 (not noquestions))
		(unwind-protect
		    (save-some-buffers)))
	    ;; Tell the prover 
	    (proof-shell-invisible-command 
	     (proof-format-filename proof-shell-inform-file-processed-cmd 
				    cfile) 
	     'wait))))))

(defun proof-inform-prover-file-retracted (rfile)
  (if proof-shell-inform-file-retracted-cmd
      (proof-shell-invisible-command
       (proof-format-filename proof-shell-inform-file-retracted-cmd 
			      rfile)
       'wait)))

(defun proof-auto-retract-dependencies (cfile &optional informprover)
  "Perhaps automatically retract the (linear) dependencies of CFILE.
If proof-auto-multiple-files is nil, no action is taken.
If CFILE does not appear on proof-included-files-list, no action taken.

Any buffers which are visiting files in proof-included-files-list
before CFILE are retracted using proof-protected-process-or-retract.
They are retracted in reverse order.

Since the proof-included-files-list is examined, we expect scripting
to be turned off before calling here (because turning it off could
otherwise change proof-included-files-list).

If INFORMPROVER is non-nil,  the proof assistant will be told about this,
using proof-shell-inform-file-retracted-cmd, to co-ordinate with its 
internal file-management.

Files which are not visited by any buffer are not retracted, on the
basis that we may not have the information necessary to retract them
-- spans that cover the buffer with definition/declaration
information.  A warning message is given for these cases, since it
could cause inconsistency problems.

NB!  Retraction can cause recursive calls of this function.
This is a subroutine for proof-unregister-buffer-file-name."
  (if proof-auto-multiple-files
      (let ((depfiles (reverse
		       (cdr-safe
			(member cfile (reverse proof-included-files-list)))))
	    rfile rbuf)
	(while (setq rfile (car-safe depfiles))
	  ;; If there's a buffer visiting a dependent file, retract it.
	  ;; We test that the file to retract hasn't been retracted
	  ;; already by a recursive call here.  (But since we do retraction
	  ;; in reverse order, this shouldn't happen...)
	  (if (and (member rfile proof-included-files-list) 
		   (setq rbuf (proof-file-to-buffer rfile)))
	      (progn
		(proof-debug "Automatically retracting " rfile)
		(proof-protected-process-or-retract 'retract rbuf)
		(setq proof-included-files-list 
		      (delete rfile proof-included-files-list))
		;; Tell the proof assistant, if we should and we can.
		;; This may be useful if we synchronise the *prover* with
		;; PG's management of multiple files.  If the *prover*
		;; informs PG (better case), then we hope the prover will
		;; retract dependent files and we shouldn't use this
		;; degenerate (linear dependency) code.
		(if informprover
		    (proof-inform-prover-file-retracted rfile)))
	    ;; If no buffer available, issue a warning that nothing was done
	    (proof-warning "Not retracting unvisited file " rfile))
	  (setq depfiles (cdr depfiles))))))

(defun proof-unregister-buffer-file-name (&optional informprover)
  "Remove current buffer's filename from the list of included files.
No effect if the current buffer has no file name.
If INFORMPROVER is non-nil,  the proof assistant will be told about this,
using proof-shell-inform-file-retracted-cmd, to co-ordinate with its 
internal file-management.

If proof-auto-multiple-files is non-nil, any buffers on 
proof-included-files-list before this one will be automatically
retracted using proof-auto-retract-dependencies."
  (if buffer-file-name
      (let ((cfile (file-truename buffer-file-name)))
	(proof-debug (concat "Unregistering file " cfile 
			       (if (not (member cfile 
						proof-included-files-list))
				   " (not registered, no action)." ".")))
	(if (member cfile proof-included-files-list)
	    (progn
	      (proof-auto-retract-dependencies cfile informprover)
	      (setq proof-included-files-list
		    (delete cfile proof-included-files-list))
	      ;; Tell the proof assistant, if we should and we can.
	      ;; This case may be useful if there is a combined 
	      ;; management of multiple files between PG and prover.
	      (if informprover
		  (proof-inform-prover-file-retracted cfile)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Activating and Deactivating Scripting
;;
;; 
;; da: cleaned

(defun proof-protected-process-or-retract (action &optional buffer)
  "If ACTION='process, process, If ACTION='retract, retract.
Process or retract the current buffer, which should be the active
scripting buffer, according to ACTION.
Retract buffer BUFFER if set, otherwise use the current buffer.
Gives a message in the minibuffer and busy-waits for the retraction
or processing to complete.  If it fails for some reason, 
an error is signalled here."
  (let ((fn   (cond ((eq action 'process) 'proof-process-buffer)
		    ((eq action 'retract) 'proof-retract-buffer)))
	(name (cond ((eq action 'process) "Processing")
		    ((eq action 'retract) "Retracting")))
	(buf  (or buffer (current-buffer))))
    (if fn
	(unwind-protect
	    (with-current-buffer buf
	      (message "%s buffer %s..." name buf)
	      (funcall fn)
	      (while proof-shell-busy ; busy wait
		(sit-for 1))
	      (message "%s buffer %s...done." name buf)
	      (sit-for 0))
	  ;; Test to see if action was successful
	  (with-current-buffer buf
	    (or (and (eq action 'retract) (proof-locked-region-empty-p))
		(and (eq action 'process) (proof-locked-region-full-p))
		(error "%s of %s failed!" name buf)))))))


(defun proof-deactivate-scripting (&optional forcedaction)
  "Deactivate scripting for the active scripting buffer.

Set proof-script-buffer to nil and turn off the modeline indicator.
No action if there is no active scripting buffer.  

We make sure that the active scripting buffer either has no locked
region or a full locked region (everything in it has been processed).
If this is not already the case, we question the user whether to
retract or assert, or automatically take the action indicated in the
user option `proof-auto-action-when-deactivating-scripting.'

If the scripting buffer is (or has become) fully processed, and it is
associated with a file, it is registered on
`proof-included-files-list'.  Conversely, if it is (or has become)
empty, we make sure that it is *not* registered.  This is to be
certain that the included files list behaves as we might expect with
respect to the active scripting buffer, in an attempt to harmonize
mixed scripting and file reading in the prover.

This function either succeeds, fails because the user refused to
process or retract a partly finished buffer, or gives an error message
because retraction or processing failed.  If this function succeeds,
then proof-script-buffer is nil afterwards.

The optional argument FORCEDACTION overrides the user option
`proof-auto-action-when-deactivating-scripting' and prevents
questioning the user.  It is used to make a value for
the kill-buffer-hook for scripting buffers, so that when
a scripting buffer is killed it is always retracted."
  (interactive)
  (if proof-script-buffer
      (with-current-buffer proof-script-buffer
	;; Examine buffer.

	;; We must ensure that the locked region is either 
	;; empty or full, to make sense for multiple-file
	;; scripting.  (A proof assistant won't be able to
	;; process just part of a file typically; moreover
	;; switching between buffers during a proof makes
	;; no sense.)
	(if (or (proof-locked-region-empty-p) 
		(proof-locked-region-full-p)
		;; Buffer is partly-processed
		(let*
		    ((action 
		      (or
		       forcedaction
		       proof-auto-action-when-deactivating-scripting
		       (progn
			 (save-window-excursion
			   (unless
			       ;; Test to see whether to display the 
			       ;; buffer or not.
			       ;; Could have user option here to avoid switching
			       ;; or maybe borrow similar standard setting
			       ;; save-some-buffers-query-display-buffer
			       (or
				(eq (current-buffer)
				    (window-buffer (selected-window)))
				(eq (selected-window) (minibuffer-window)))
			     (progn
			       (unless (one-window-p)
				 (delete-other-windows))
			       (switch-to-buffer proof-script-buffer t)))
			   ;; Would be nicer to ask a single question, but
			   ;; a nuisance to define our own dialogue since it
			   ;; doesn't really fit with one of the standard ones.
			   (cond
			    ((y-or-n-p
			      (format
			       "Scripting incomplete in buffer %s, retract? "
			       proof-script-buffer))
			     'retract)
			    ((y-or-n-p
			      (format
			       "Completely process buffer %s instead? "
			       proof-script-buffer))
			     'process)))))))
		  ;; Take the required action
		  (if action
		      (proof-protected-process-or-retract action)
		    ;; Give an acknowledgement to user's choice
		    ;; neither to assert or retract.  
		    (message "Scripting still active in %s" 
			     proof-script-buffer)
		    ;; Delay because this can be followed by an error
		    ;; message in proof-activate-scripting when trying
		    ;; to switch to another scripting buffer.
		    (sit-for 1)
		    nil)))

	    ;; If we get here, then the locked region is (now) either 
	    ;; completely empty or completely full.  
	    (progn
	      ;; We can immediately indicate that there is no active
	      ;; scripting buffer
	      (setq proof-script-buffer nil)

	      (if (proof-locked-region-full-p)
		  ;; If locked region is full, make sure that this buffer
		  ;; is registered on the included files list, and
		  ;; let the prover know it can consider it processed.
		  (if buffer-file-name
		      (proof-register-possibly-new-processed-file 
		       buffer-file-name
		       'tell-the-prover
		       forcedaction)))
	      
	      (if (proof-locked-region-empty-p)
		  ;; If locked region is empty, make sure this buffer is
		  ;; *off* the included files list. 
		  ;; FIXME: probably this isn't necessary: the
		  ;; file should be unregistered by the retract
		  ;; action, or in any case since it was only
		  ;; partly processed.
		  ;; FIXME 2: be careful about automatic
		  ;; multiple file handling here, since it calls
		  ;; for activating scripting elsewhere.
		  ;; We move the onus on unregistering now to
		  ;; the activate-scripting action.
		  (proof-unregister-buffer-file-name))

	      ;; Turn off Scripting indicator here.
	      (setq proof-active-buffer-fake-minor-mode nil)

	      ;; Make status of inactive scripting buffer show up
	      ;; FIXME da:
	      ;; not really necessary when called by kill buffer, at least.
	      (if (fboundp 'redraw-modeline)
		  (redraw-modeline)
		(force-mode-line-update)))))))
  
(defun proof-activate-scripting (&optional nosaves queuemode)
  "Ready prover and activate scripting for the current script buffer.

The current buffer is prepared for scripting. No changes are
necessary if it is already in Scripting minor mode. Otherwise, it
will become the new active scripting buffer, provided scripting
can be switched off in the previous active scripting buffer
with `proof-deactivate-scripting'.

Activating a new script buffer may be a good time to ask if the 
user wants to save some buffers; this is done if the user
option `proof-query-file-save-when-activating-scripting' is set
and provided the optional argument NOSAVES is non-nil.

The optional argument QUEUEMODE relaxes the test for a
busy proof shell to allow one which has mode QUEUEMODE.
In all other cases, a proof shell busy error is given.

Finally, the hooks `proof-activate-scripting-hook' are run.  
This can be a useful place to configure the proof assistant for
scripting in a particular file, for example, loading the
correct theory, or whatever.  If the hooks issue commands
to the proof assistant (via `proof-shell-invisible-command')
which result in an error, the activation is considered to
have failed and an error is given."
  (interactive)
  ;; FIXME: the scope of this save-excursion is rather wide.
  ;; Problems without it however: Use button behaves oddly
  ;; when process is started already.
  ;; Where is save-excursion needed?
  ;; First experiment shows that it's the hooks that cause
  ;; problem, maybe even the use of proof-cd-sync (can't see why).
  (save-excursion
    ;; FIXME: proof-shell-ready-prover here s
    (proof-shell-ready-prover queuemode)
    (cond 
     ((not (eq proof-buffer-type 'script)) 
      (error "Must be running in a script buffer!"))
     
     ;; If the current buffer is the active one there's nothing to do.
   ((equal (current-buffer) proof-script-buffer))
     
     ;; Otherwise we need to activate a new Scripting buffer.
   (t
      ;; If there's another buffer currently active, we need to 
      ;; deactivate it (also fixing up the included files list).
      (if proof-script-buffer
	  (progn
	    (proof-deactivate-scripting)
	    ;; Test whether deactivation worked
	    (if proof-script-buffer
		(error 
		 "You cannot have more than one active scripting buffer!"))))
	    
      ;; Now make sure that this buffer is off the included files
      ;; list.  In case we re-activate scripting in an already
      ;; completed buffer, it may be that the proof assistant
      ;; needs to retract some of this buffer's dependencies.
      (proof-unregister-buffer-file-name 'tell-the-prover)

      ;; If automatic retraction happened in the above step, we may
      ;; have inadvertently activated scripting somewhere else.
      ;; Better turn it off again.   This should succeed trivially.
      ;; NB: it seems that we could move the first test for an already
      ;; active buffer here, but it is more subtle: the first
      ;; deactivation can extend the proof-included-files list, which
      ;; would affect what retraction was done in
      ;; proof-unregister-buffer-file-name.
      (if proof-script-buffer
	  (proof-deactivate-scripting))
      (assert (null proof-script-buffer) 
	      "Bug in proof-activate-scripting: deactivate failed.")

      ;; Set the active scripting buffer, and initialise the 
      ;; queue and locked regions if necessary.
      (setq proof-script-buffer (current-buffer))
      (if (proof-locked-region-empty-p)
	  ;; This removes any locked region that was there, but
	  ;; sometimes we switch on scripting in "full" buffers,
	  ;; so mustn't do this.
	  (proof-init-segmentation))

      ;; Turn on the minor mode, make it show up.
      (setq proof-active-buffer-fake-minor-mode t)
      (if (fboundp 'redraw-modeline)
	  (redraw-modeline)
	(force-mode-line-update))
      
      ;; This may be a good time to ask if the user wants to save some
      ;; buffers.  On the other hand, it's jolly annoying to be
      ;; queried on the active scripting buffer if we've started
      ;; writing in it.  So pretend that one is unmodified, at least
      ;; (we certainly don't expect the proof assitant to load it)
      (if (and
	   proof-query-file-save-when-activating-scripting
	   (not nosaves))
	  (let ((modified (buffer-modified-p)))
	    (set-buffer-modified-p nil)
	    (unwind-protect
		(save-some-buffers)
 	      (set-buffer-modified-p modified))))

      ;; Run hooks with a variable which suggests whether or not 
      ;; to block.   NB: The hook function may send commands to the
      ;; process which will re-enter this function, but should exit 
      ;; immediately because scripting has been turned on now.
      (if proof-activate-scripting-hook
	  (let
	      ((activated-interactively	(interactive-p)))
	    ;; Clear flag in case no hooks run shell commands
	    (setq proof-shell-error-or-interrupt-seen nil)
	    (run-hooks 'proof-activate-scripting-hook)
	    ;; In case the activate scripting functions
	    ;; caused an error in the proof assistant, we'll
	    ;; consider activating scripting to have failed,
	    ;; and raise an error here.
	    ;; (Since this behaviour is intimate with the hook functions,
	    ;;  it could be removed and left to implementors of 
	    ;;  specific instances of PG).
	    ;; FIXME: we could consider simply running the hooks
	    ;; as the last step before turning on scripting properly,
	    ;; provided the hooks don't inspect proof-script-buffer.
	    (if proof-shell-error-or-interrupt-seen
		(progn
		  (proof-deactivate-scripting) ;; turn it off again!
		  ;; Give an error to prevent further actions.
		  (error "Proof General: Scripting not activated because of error or interrupt.")))))))))


(defun proof-toggle-active-scripting (&optional arg)
  "Toggle active scripting mode in the current buffer.
With ARG, turn on scripting iff ARG is positive."
  (interactive "P")
  ;; A little less obvious than it may seem: toggling scripting in the
  ;; current buffer may involve turning it off in some other buffer
  ;; first!
  (if (if (null arg)
	  (not (eq proof-script-buffer (current-buffer)))
	(> (prefix-numeric-value arg) 0))
      (progn
	(if proof-script-buffer 
	    (call-interactively 'proof-deactivate-scripting))
	(call-interactively 'proof-activate-scripting))
    (call-interactively 'proof-deactivate-scripting)))

;; This function isn't such a wise idea: the buffer will often be fully
;; locked when writing a script, but we don't want to keep toggling
;; switching mode!
;;(defun proof-auto-deactivate-scripting ()
;;  "Turn off scripting if the current scripting buffer is empty or full.
;;This is a possible value for proof-state-change-hook.
;;FIXME: this currently doesn't quite work properly as a value for 
;;proof-state-change-hook, in fact: maybe because the
;;hook is called somewhere where proof-script-buffer
;;should not be nullified!"
;;  (if proof-script-buffer
;;      (with-current-buffer proof-script-buffer
;;	(if (or (proof-locked-region-empty-p)
;;		(proof-locked-region-full-p))
;;	    (proof-deactivate-scripting)))))

;;
;;  End of activating and deactivating scripting section
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; da: NEW function added 28.10.98.
;; This is used by toolbar follow mode (which used to use the function
;; above).  [But wouldn't work for proof-shell-handle-error-or-interrupt-hook?].

(defun proof-goto-end-of-queue-or-locked-if-not-visible ()
  "Jump to the end of the queue region or locked region if it isn't visible.
Assumes script buffer is current"
  (unless (pos-visible-in-window-p
	   (proof-queue-or-locked-end)
	   (get-buffer-window (current-buffer) t))
    (goto-char (proof-queue-or-locked-end))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          User Commands                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
; Script management uses two major segments: Locked, which marks text
; which has been sent to the proof assistant and cannot be altered
; without being retracted, and Queue, which contains stuff being
; queued for processing.  proof-action-list contains a list of
; (span,command,action) triples. The loop looks like: Execute the
; command, and if it's successful, do action on span.  If the
; command's not successful, we bounce the rest of the queue and do
; some error processing.
;
; when a span has been processed, we classify it as follows:
; 'proof - denoting a 'proof pair in the locked region
;    a 'proof region has a 'name property which is the name of the goal
; 'comment - denoting a comment
; 'pbp - denoting a span created by pbp
; 'vanilla - denoting any other span.
; 'proverproc -- prover processed region (e.g. when a file is read
;			atomically by the prover)
;   'pbp & 'vanilla spans have a property 'cmd, which says what
;   command they contain. 




; We don't allow commands while the queue has anything in it.  So we
; do configuration by concatenating the config command on the front in
; proof-shell-insert

;;         proof-assert-until-point, and various gunk for its       ;;
;;         setup and callback                                       ;;


(defun proof-check-atomic-sequents-lists (span cmd end)
  "Check if CMD is the final command in an ACS.

If CMD is matched by the end regexp in `proof-atomic-sequents-list',
the ACS is marked in the current buffer. If CMD does not match any,
`nil' is returned, otherwise non-nil."
  ;;FIXME tms: needs implementation
  nil)



(defun proof-done-advancing (span)
  "The callback function for assert-until-point."
  ;; FIXME da: if the buffer dies, this function breaks horribly.
  ;; Needs robustifying.
  (if (not (span-live-p span))
      ;; FIXME da: Sometimes this function is called with a destroyed
      ;; extent as argument.  When?  Isn't this a bug?
      ;; (one case would be if the buffer is killed while
      ;; a proof is completing)
      ;; NB: this patch doesn't work!  Are spans being destroyed
      ;; sometime *during* this code??
      (proof-debug 
       "Proof General idiosyncrasy: proof-done-advancing called with a dead span!")
  ;; 
  (let ((end (span-end span)) cmd)
    ;; State of spans after advancing: 
    (proof-set-locked-end end)
    (proof-set-queue-start end)
    (setq cmd (span-property span 'cmd))
    (cond
     ;; CASE 1: Comments just get highlighted
     ((eq (span-property span 'type) 'comment)
      (set-span-property span 'mouse-face 'highlight))
     
     ;; CASE 2: Save command seen, now we'll amalgamate spans.
     ((and proof-save-command-regexp
	   (proof-string-match proof-save-command-regexp cmd)
	    (funcall proof-really-save-command-p span cmd))

      (unless (eq proof-shell-proof-completed 1)
	;; We expect saves to succeed only for recently completed proofs.
	;; Give a hint to the proof assistant implementor in case something
	;; odd is going on.
	(proof-debug 
	 (format
	  "Proof General note: save command with proof-shell-proof-completed=%s"
	  proof-shell-proof-completed)))

      (setq proof-shell-proof-completed nil)

      ;; FIXME: subroutine here:
      (let (nam gspan next)

	;; Try to set the name of the theorem from the save
	(message "%s" cmd)

	(and proof-save-with-hole-regexp
	     (proof-string-match proof-save-with-hole-regexp cmd)
	     (setq nam 
		   (if (stringp proof-save-with-hole-result)
		       (replace-match proof-save-with-hole-result nil nil cmd)
		     (match-string proof-save-with-hole-result cmd))))
	(message "%s" nam)
	;; Search backwards for first goal command, 
	;; deleting spans along the way.
	(setq gspan span)
	(while (and gspan
		    (or (eq (span-property gspan 'type) 'comment)
			(not (funcall proof-goal-command-p 
				      (setq cmd (span-property gspan 'cmd))))))
	  (setq next (prev-span gspan 'type))
	  (delete-span gspan)
	  (setq gspan next))
	(if (not gspan)
	    ;; No goal span found!  Issue a warning and do nothing more.
	    (proof-warning
	     "Proof General: script management confused, couldn't find goal span for save.")

	;; If the name isn't set, try to set it from the goal. 
	  (unless nam
	    (let ((cmdstr (span-property gspan 'cmd)))
	      (message "%s" cmdstr)
	      (and proof-goal-with-hole-regexp
		   (proof-string-match proof-goal-with-hole-regexp cmdstr)
		   (setq nam 
			 (if (stringp proof-goal-with-hole-result)
			     (replace-match proof-goal-with-hole-result nil nil cmdstr)
			   (match-string proof-goal-with-hole-result cmdstr))))))
	  
	;; As a final desparate attempt, set the name to
	;; proof-unnamed-theorem-name (Coq actually uses a default
	;; name for unnamed theorems, believe it or not, and issues
	;; a name-binding error for two unnamed theorems in a row!).
	(unless nam
	  (setq nam proof-unnamed-theorem-name))

	;; FIXME: this needs to be abstracted out into a function
	;; pg-add-new-proof-span

	;; Now make the new goal-save span
	(set-span-end gspan end)
	(set-span-property gspan 'mouse-face 'highlight)
	(set-span-property gspan 'type 'proof)
	(set-span-property gspan 'name nam)


	;; Set the context sensitive menu/keys
	(set-span-property gspan 'keymap span-context-menu-keymap)
	
	;; Add to buffer-local list of elements, maybe making invisible
	(pg-add-proof-element nam gspan)

	;; *** Theorem dependencies ***
	;; Dependencies returns a list of strings, each string being
	;; the name of a dependency of that span 
	;; depcs-within-file returns the names of all the theorems that
	;; the span depends on which are in the same file as the theorem.

	(if proof-last-theorem-dependencies
	    (progn 
	      (if (boundp 'proof-deps-menu) 
		  (easy-menu-remove proof-deps-menu))
	      (set-span-property gspan 'dependencies 
				 proof-last-theorem-dependencies)
	      (set-span-property gspan 'keymap span-context-menu-keymap)
	      (if buffer-file-name
		  (let* 
		      ((buffer-file-name-sans-path
			(car (last (split-string buffer-file-name "/"))))
		       (buffer-file-name-sans-extension
			(car (split-string buffer-file-name-sans-path "\\.")))
		       (depcs-within-file-list 
			(dependencies-within-file-list 
			 proof-last-theorem-dependencies 
			 buffer-file-name-sans-extension)))
		    (set-span-property gspan 'dependencies-within-file
				       depcs-within-file-list)
		    (update-dependents depcs-within-file-list 
				       buffer-file-name-sans-path 
				       buffer-file-name-sans-extension 
				       (span-property gspan 'name))
		    (proof-menu-define-deps buffer-file-name-sans-path)
		    (easy-menu-add proof-deps-menu proof-mode-map)
		    ;; FIXME: this is Isabelle specific, needs moving out
		    (let ((thy-file (concat 
				     buffer-file-name-sans-extension ".thy")))
		      (find-file-noselect thy-file)
		      (save-excursion
			(set-buffer thy-file)
			(thy-add-menus buffer-file-name-sans-path)))))
	      ;; da: this code was outside if, I've put it inside now
	      (setq proof-last-theorem-dependencies nil)
	      (setq proof-thm-names-of-files 
		    (merge-names-list-it (span-property gspan 'name) 
					 (buffer-name (span-object gspan)) 
					 proof-thm-names-of-files))))

	;; In Coq, we have the invariant that if we've done a save and
	;; there's a top-level declaration then it must be the
	;; associated goal.  (Notice that because it's a callback it
	;; must have been approved by the theorem prover.)
	(and proof-lift-global
	     (funcall proof-lift-global gspan)))))

     ;; CASE 3: Proof completed one step or more ago, non-save
     ;; command seen, no nested goals allowed.
     ;; 
     ;; We make a fake goal-save from any previous 
     ;; goal to the command before the present one.
     ;;
     ;; This is a hack to allow smooth undoing in proofs which have no
     ;; "qed" statements.  If your proof assistant doesn't allow
     ;; these "unclosed" proofs, then you can safely set
     ;; proof-completed-proof-behaviour.
     ;;
     ;; FIXME: abstract common part of this case and case above,
     ;; to improve code by making a useful subroutine.
     ((and
       proof-shell-proof-completed
       (or (and (eq proof-completed-proof-behaviour 'extend)
		(>= proof-shell-proof-completed 0))
	   (and (eq proof-completed-proof-behaviour 'closeany)
		(> proof-shell-proof-completed 0))
	   (and (eq proof-completed-proof-behaviour 'closegoal)
		(funcall proof-goal-command-p cmd))))

      (if (eq proof-completed-proof-behaviour 'extend)
	  ;; In the extend case, the context of the proof grows
	  ;; until we hit a save or new goal.
	  (incf proof-shell-proof-completed)
	(setq proof-shell-proof-completed nil))

      (let* ((swallow  (eq proof-completed-proof-behaviour 'extend))
	     (gspan    (if swallow span (prev-span span 'type)))
	     (newend   (if swallow (span-end span) (span-start span)))
	    nam hitsave dels)
	;; Search backwards to see if we can find a previous goal
	;; before a save or the start of the buffer.
	(while 
	    (and 
	     gspan
	     (or 
	      (eq (span-property gspan 'type) 'comment)
	      (and
	       (not (funcall proof-goal-command-p 
			     (setq cmd (span-property gspan 'cmd))))
	       (not
		(and proof-save-command-regexp
		     (proof-string-match proof-save-command-regexp cmd)
		     (funcall proof-really-save-command-p span cmd)
		     (setq hitsave t))))))
	  (setq dels (cons gspan dels))
	  (setq gspan (prev-span gspan 'type)))
	(if (or hitsave (null gspan))
	    (proof-debug
     "Proof General strangeness: unclosed proof completed, but couldn't find its start!")
	  ;; If we haven't hit a save or the start of the buffer,
	  ;; we make a fake goal-save region.

	  ;; Delete spans between the previous goal and new command
	  (mapcar 'delete-span dels)

	  ;; Try to set a name from the goal
	  ;; (useless for provers like Isabelle)
	  (let ((cmdstr (span-property gspan 'cmd)))
	    (message "%s" cmdstr)
	    (and proof-goal-with-hole-regexp
		 (proof-string-match proof-goal-with-hole-regexp cmdstr)
		 (setq nam 
		       (if (stringp proof-goal-with-hole-result)
			   (replace-match proof-goal-with-hole-result nil nil cmdstr)
			 (match-string proof-goal-with-hole-result cmdstr)))))

	  ;; As a final desparate attempt, set the name to "Unnamed_thm".
	  (unless nam
	    (setq nam proof-unnamed-theorem-name))
	  
	  ;; Now make the new or extended goal-save span
	  ;; Don't bother with Coq's lift global stuff, we assume this
	  ;; case is only good for non-nested goals.
	  (set-span-end gspan newend)
	  (set-span-property gspan 'mouse-face 'highlight)
	  (set-span-property gspan 'type 'proof)
	  (set-span-property gspan 'name nam))
	;; Finally, do the usual thing with highlighting for the span.
	(unless swallow
	  (set-span-property span 'mouse-face 'highlight))))


     ;; "ACS" for possible future implementation
     ;; ((proof-check-atomic-sequents-lists span cmd end))

     ;; CASE 4:  Some other kind of command (or a nested goal).
     (t
      (if proof-shell-proof-completed
	  (incf proof-shell-proof-completed))
      (set-span-property span 'mouse-face 'highlight)
      (and proof-global-p 
	   (funcall proof-global-p cmd)
	   proof-lift-global
	   (funcall proof-lift-global span)))))

  ;; State of scripting may have changed now
  (run-hooks 'proof-state-change-hook)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Yet more NEW parsing functions for 3.3
;;
;; We need to be more general and a bit more clear, this
;; is a much better attempt.

(defun proof-segment-up-to-parser (pos &optional next-command-end)
  "Parse the script buffer from end of locked to POS.
Return a list of (type, string, int) tuples (in reverse order).

Each tuple denotes the command and the position of its final character,
type is one of 'comment, or 'cmd.

The behaviour around comments is set by
`proof-script-fly-past-comments', which see.

This version is used when `proof-script-parse-function' is set,
to the function which parses the script segment by segment."
  (save-excursion
    (let* ((start (goto-char (proof-queue-or-locked-end)))
	   (cur   (1- start))
	   (seg   t)
	   prevtype realstart cmdseen segs)
      ;; Keep parsing until:
      ;;   - we fail to find a segment   (seg = nil)
      ;;   - we go beyond the stop point (cur >= end)
      ;;      - unless we're flying past comments, in which case
      ;;        wait for a command (cmdseen<>nil)
      (while (and seg 
		  (or (< cur pos) 
		      (and proof-script-fly-past-comments
			   (not cmdseen))))
	;; Skip whitespace before this element
	(skip-chars-forward " \t\n")
	(setq realstart (point))
	(let* ((type  (funcall proof-script-parse-function)))
	  (setq seg nil)
	  (cond
	   ((eq type 'comment)
	    (setq seg (list 'comment "" (point))))
	   ((eq type 'cmd)
	    (setq cmdseen t)
	    (setq seg (list 
		       'cmd 
		       (buffer-substring realstart (point)) 
		       (point))))
	   ((null type))		; nothing left in buffer
	   (t 
	    (error 
  "proof-segment-up-to-parser: bad TYPE value from proof-script-parse-function.")))
	  ;;
	  (if seg 
	      (progn
		;; Add the new segment, coalescing comments if
		;; the user likes it that way.  I first made
		;; coalescing a separate configuration option, but
		;; it works well used in tandem with the fly-past
		;; behaviour.
		(if (and proof-script-fly-past-comments
			 (eq type 'comment)
			 (eq prevtype 'comment))
		    (setq segs (cons seg (cdr segs)))
		  (setq segs (cons seg segs)))
		;; Update state
		(setq cur (point))
		(setq prevtype type)))))
      ;; Return segment list
      segs)))

(defun proof-script-generic-parse-find-comment-end ()
  "Find the end of the comment point is at the start of. Nil if not found."
  (let ((notout t))
    ;; Find end of comment (NB: doesn't undertand nested comments)
    (while (and notout (re-search-forward 
			proof-comment-end-regexp nil 'movetolimit))
      (setq notout (proof-buffer-syntactic-context)))
    (not (proof-buffer-syntactic-context))))
  
(defun proof-script-generic-parse-cmdend ()
  "Used for proof-script-parse-function if proof-script-command-end-regexp is set."
  (if (looking-at proof-comment-start-regexp)
      ;; Handle comments
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    ;; Handle non-comments: assumed to be commands
    (let (foundend)
      ;; Find end of command
      (while (and (setq foundend 
			(re-search-forward proof-script-command-end-regexp nil t))
		  (proof-buffer-syntactic-context))
	;; inside a string or comment before the command end
	)
      (if (and foundend 
	       (not (proof-buffer-syntactic-context)))
	  ;; Found command end outside string/comment
	  'cmd
	;; Didn't find command end
	nil))))

(defun proof-script-generic-parse-cmdstart ()
  "For proof-script-parse-function if proof-script-command-start-regexp is set."
  ;; This was added for the fine-grained command structure of Isar
  ;;
  ;; It's is a lot more involved than the case of just scanning for
  ;; the command end; we have to find two successive command starts
  ;; and go backwards from the second.  This coalesces comments
  ;; following commands with commands themselves, and sends them to
  ;; the prover (only case where it does).
  ;;
  ;; To avoid doing that, we would need to scan also for comments but
  ;; it would be difficult to distinguish between:
  ;;   complete command (* that's it *)
  ;; and
  ;;   complete (* almost *) command
  ;;
  ;; Maybe the second case should be disallowed in command-start regexp case?
  ;; 
  ;; Another improvement idea might be to take into account both
  ;; command starts *and* ends, but let's leave that for another day.
  ;;
  (if (looking-at proof-comment-start-regexp)
      ;; Find end of comment
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    ;; Handle non-comments: assumed to be commands
    (if (looking-at proof-script-command-start-regexp)
	(progn
	  ;; We've got at least the beginnings of a command, skip past it
	  (re-search-forward proof-script-command-start-regexp nil t)
	  (let (foundstart)
	    ;; Find next command start
	    (while (and (setq 
			 foundstart 
			 (and 
			  (re-search-forward proof-script-command-start-regexp
					     nil 'movetolimit)
			  (match-beginning 0)))
			(proof-buffer-syntactic-context))
	      ;; inside a string or comment before the next command start
	      )
	    (if (not (proof-buffer-syntactic-context))  ; not inside a comment/string
		(if foundstart		             ; found a  second command start
		    (progn
		      (goto-char foundstart)          ; beginning of command start
		      (skip-chars-backward " \t\n")   ; end of previous command
		      'cmd)
		  (if (eq (point) (point-max)) ; At the end of the buffer
		      (progn
			(skip-chars-backward " \t\n") ; benefit of the doubt, let 
			'cmd))))		      ; the PA moan if it's incomplete
	    ;; Return nil in other cases, no complete command found
	    )))))


(defun proof-script-generic-parse-sexp ()
  "Used for proof-script-parse-function if proof-script-sexp-commands is set."
  ;; Usual treatment of comments
  (if (looking-at proof-comment-start-regexp)
      ;; Find end of comment
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    (let* ((parse-sexp-ignore-comments t)	; gobble comments into commands
	   (end (scan-sexps (point) 1)))
      (if end
	  (progn (goto-char end) 'cmd)))))
    

;; NEW parsing functions for 3.2
;;
;; NB: compared with old code,
;; (1) this doesn't treat comments quite so well, but parsing
;; should be rather more efficient.
;; (2) comments are treated less like commands, and are only
;; coloured blue "in passing" when commands are sent.
;; However, undo still process comments step-by-step.

(defun proof-segment-up-to-cmdstart (pos &optional next-command-end)
  "Parse the script buffer from end of locked to POS.
Return a list of (type, string, int) tuples.

Each tuple denotes the command and the position of its terminator,
type is one of 'comment, or 'cmd.

If optional NEXT-COMMAND-END is non-nil, we include the command
which continues past POS, if any.  (NOT IMPLEMENTED IN THIS VERSION).

This version is used when `proof-script-command-start-regexp' is set."
  (save-excursion
    (let* ((commentre   (concat "[ \t\n]*" proof-comment-start-regexp))
	   (commentend   (concat proof-comment-end-regexp "[ \t\n]*" ))
	   (add-segment-for-cmd		; local function: advances "prev"
	    (lambda ()
	      (setq tmp (point))
	      ;; Find end of previous command...
	      (goto-char comstart)
	      ;; Special hack: allow terminal char to be included
	      ;; in a command, if it's set.
	      (if (and proof-terminal-char
		       (looking-at 
			(regexp-quote (char-to-string proof-terminal-char))))
		  (goto-char (1+ (point)))
		(skip-chars-backward " \t\n"))
	      (let* ((prev-no-blanks
		      (save-excursion 
			(goto-char prev) 
			(skip-chars-forward " \t\n") 
			(point)))
		     (comend (point))
		     (bufstr (buffer-substring prev-no-blanks comend))
		     (type   (save-excursion
				  ;; The behaviour here is a bit odd: this
				  ;; is a half-hearted attempt to strip comments
				  ;; as we send text to the proof assistant,
				  ;; but it breaks when we have certain bad
				  ;; input:  (* foo *) blah (* bar *) cmd 
				  ;; We check for the case
				  ;; of a comment spanning the *whole*
				  ;; substring, otherwise send the
				  ;; (defective) text as if it were a
				  ;; proper command anyway.
				  ;; This shouldn't cause problems: the 
				  ;; proof assistant is certainly capable
				  ;; of skipping comments itself, and
				  ;; the situation should cause an error.
				  ;; (If it were accepted it could upset the
				  ;; undo behaviour)
			       (goto-char prev-no-blanks)
			       (if (and 
				    (looking-at commentre)
				    (re-search-forward proof-comment-end-regexp)
				    (skip-chars-forward " \t\n")
				    (>= (point) comend))
				   'comment 'cmd)))
		     (string (if (eq type 'comment) "" bufstr)))
		(setq prev (point))
		(goto-char tmp)
		;; NB: Command string excludes whitespace, span includes it.
		(setq alist (cons (list type string prev) alist)))))
	   alist prev cmdfnd startpos comstart tmp)
      (goto-char (proof-queue-or-locked-end))
      (setq prev (point))
      (skip-chars-forward " \t\n")
      (setq startpos (point))
      (while 
	  (and 
	   (proof-re-search-forward proof-script-command-start-regexp
			      nil t)   ; search for next command
	   (setq comstart (match-beginning 0)); save command start
	   (or (save-excursion
		 (goto-char comstart)
		 ;; continue if inside (or at start of) comment/string
		 (proof-looking-at-syntactic-context))
	       (progn			    ; or, if found command...
		 (setq cmdfnd 
		       (> comstart startpos)); ignore first match
		 (<= prev pos))))
	(if cmdfnd (progn
		     (funcall add-segment-for-cmd)
		     (setq cmdfnd nil))))
      ;; End of parse; see if we found some text at the end of the
      ;; buffer which could be a command.  (NB: With a regexp for 
      ;; start of commands only, we can't be sure it is a complete
      ;; command).
      (if (and comstart			; previous command was found
	       (<= prev pos)		; last command within range
	       (goto-char (point-max))
	       (setq comstart (point))	; pretend there's another cmd here
	       (not (proof-buffer-syntactic-context))) ; buffer ends well
	  (funcall add-segment-for-cmd))
      ; (if (and cmdfnd next-command-end)
      ; (funcall add-segment-for-cmd))
      ;; Return resulting list
      alist)))


;; FIXME: this needs fixing to include final comment in buffer
;; if there is one!!

(defun proof-segment-up-to-cmdend (pos &optional next-command-end)
  "Parse the script buffer from end of locked to POS.
Return a list of (type, string, int) tuples.

Each tuple denotes the command and the position of its terminator,
type is one of 'comment, or 'cmd. 'unclosed-comment may be consed onto
the start if the segment finishes with an unclosed comment.

If optional NEXT-COMMAND-END is non-nil, we include the command
which continues past POS, if any.

This version is used when `proof-script-command-end-regexp' is set."
  (save-excursion
    (let* 
	((commentre   (concat "[ \t\n]*" proof-comment-start-regexp))
	 (add-segment-for-cmd		; local function: advances "prev"
	  (lambda ()
	    (let ((cmdend (point)) start)
	      (goto-char prev)
	      ;; String may start with comments, let's strip them off
	      (while 
		  (and
		   (setq start (point))
		   (proof-re-search-forward commentre cmdend t)
		   (or (eq (match-beginning 0) start)
		       ;; In case a comment inside a command was found, make
		       ;; sure we're at the start of the cmd before exiting
		       (progn (goto-char start) nil)))
		;; Look for the end of the comment 
		;; (FIXME: ignore nested comments here, we should
		;; have a consistent policy!)
		(unless
		    (proof-re-search-forward 
		     proof-comment-end-regexp cmdend t)
		  (error
		   "PG error: proof-segment-up-to-cmd-end didn't find comment end."))
		(setq alist (cons (list 'comment "" (point)) alist)))
	      ;; There should be something left: a command.
	      (skip-chars-forward " \t\n")
	      (setq alist (cons (list 'cmd 
				      (buffer-substring
				       (point) cmdend) 
				      cmdend) alist))
	      (setq prev cmdend)
	      (goto-char cmdend))))
	 alist prev cmdfnd startpos tmp)
      (goto-char (proof-queue-or-locked-end))
      (setq prev (point))
      (skip-chars-forward " \t\n")
      (setq startpos (point))
      (while 
	  (and 
	   (proof-re-search-forward proof-script-command-end-regexp
			      nil t) ; search for next command
	   (or (proof-buffer-syntactic-context)   ; continue if inside comment/string
	       (progn			    ; or, if found command...
		 (setq cmdfnd t)
		 (<= (point) pos))))
	(if cmdfnd (progn
		     (funcall add-segment-for-cmd)
		     (setq cmdfnd nil))))
      ;; End of parse; if we found a command past POS maybe add it.
      ;; FIXME: also, if we found a *comment* maybe add it!
      (if cmdfnd ; (and cmdfnd next-command-end)
	  (funcall add-segment-for-cmd))
      ;; Return resulting list
      alist)))

(defun proof-semis-to-vanillas (semis &optional callback-fn)
  "Convert a sequence of terminator positions to a set of vanilla extents.
Proof terminator positions SEMIS has the form returned by
the function proof-segment-up-to.
Set the callback to CALLBACK-FN or 'proof-done-advancing by default."
  (let ((ct (proof-queue-or-locked-end)) span alist semi)
    (while (not (null semis))
      (setq semi (car semis)
            span (make-span ct (nth 2 semi))
	    ct (nth 2 semi))
      (if (eq (car (car semis)) 'cmd)
	  (progn
	    (set-span-property span 'type 'vanilla)
	    (set-span-property span 'cmd (nth 1 semi))
	    (setq alist (cons (list span (nth 1 semi) 
				    (or callback-fn 'proof-done-advancing))
			      alist)))
	(set-span-property span 'type 'comment)
	(setq alist (cons (list span proof-no-command 'proof-done-advancing) 
			  alist)))
	(setq semis (cdr semis)))
    (nreverse alist)))

;;
;; Two commands for moving forwards in proof scripts.
;; Moving forward for a "new" command may insert spaces
;; or new lines.  Moving forward for the "next" command
;; does not.
;;

(defun proof-script-new-command-advance ()
  "Move point to a nice position for a new command.
Assumes that point is at the end of a command."
  (interactive)
; FIXME: pending improvement for 3.2, needs a fix here.
;  (if (eq (proof-locked-end) (point))
;      ;; A hack to fix problem that the locked span
;      ;; is [ ) so sometimes inserting at the end
;      ;; tries to extend it, giving "read only" error.
;      (if (> (point-max) (proof-locked-end))
;	  (progn
;	    (goto-char (1+ (proof-locked-end)))
;	    (backward-char))))
  (if proof-one-command-per-line
      ;; One command per line: move to next new line,
      ;; creating one if at end of buffer or at the
      ;; start of a blank line.  (This has the pleasing
      ;; effect that blank regions of the buffer are
      ;; automatically extended when inserting new commands).
; unfortunately if we're not at the end of a line to start,
; it skips past stuff to the end of the line!  don't want
; that.
;      (cond
;       ((eq (forward-line) 1)
;	(newline))
;       ((eolp)
;        (newline)
;	(forward-line -1)))
      (newline)
    ;; Multiple commands per line: skip spaces at point,
    ;; and insert the 1/0 number of spaces that were
    ;; skipped in front of point (at least one).
    ;; This has the pleasing effect that the spacing
    ;; policy of the current line is copied: e.g.
    ;;   <command>;  <command>;
    ;; Tab columns don't work properly, however.
    ;; Instead of proof-one-command-per-line we could
    ;; introduce a "proof-command-separator" to improve
    ;; this.
    (let ((newspace (max (skip-chars-forward " \t") 1))
	  (p (point)))
      (if proof-script-command-separator
	  (insert proof-script-command-separator)
	(insert-char ?\ newspace)
	(goto-char p)))))

(defun proof-script-next-command-advance ()
  "Move point to the beginning of the next command if it's nearby.
Assumes that point is at the end of a command."
  (interactive)
  ;; skip whitespace on this line
  (skip-chars-forward " \t")		
  (if (and proof-one-command-per-line (eolp))
      ;; go to the next line if we have one command per line
      (forward-line)))


;; NB: the "interactive" variant is so that we get a simple docstring.
(defun proof-assert-until-point-interactive ()
  "Process the region from the end of the locked-region until point.
Default action if inside a comment is just process as far as the start of
the comment."
  (interactive)
  (proof-assert-until-point))


; Assert until point - We actually use this to implement the 
; assert-until-point, electric terminator keypress, and goto-command-end.
; In different cases we want different things, but usually the information
; (i.e. are we inside a comment) isn't available until we've actually run
; proof-segment-up-to (point), hence all the different options when we've
; done so.

;; FIXME da: this command doesn't behave as the doc string says when
;; inside comments.  Also is unhelpful at the start of commands, and
;; in the locked region.  I prefer the new version below.

;; FIXME: get rid of duplication between proof-assert-next-command and
;; proof-assert-until-point.  Get rid of ignore process nonsense.

;; FIXME: get rid of unclosed-comment-fun nonsense.  It's used
;; in the electric terminator function, but we should probably
;; use something else for that!

(defun proof-assert-until-point (&optional unclosed-comment-fun 
					   ignore-proof-process-p)
  "Process the region from the end of the locked-region until point.
Default action if inside a comment is just process as far as the start of
the comment. 

If you want something different, put it inside
UNCLOSED-COMMENT-FUN. If IGNORE-PROOF-PROCESS-P is set, no commands
will be added to the queue and the buffer will not be activated for
scripting."
  (unless ignore-proof-process-p 
    (proof-activate-scripting nil 'advancing))
  (let ((semis))
    (save-excursion
      ;; Give error if no non-whitespace between point and end of
      ;; locked region.  
      (if (proof-only-whitespace-to-locked-region-p)
	  (error "At the end of the locked region already, there's nothing to do to!"))
      ;; NB: (point) has now been moved backwards to first non-whitespace char.
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (null semis))
	  ;; This is another case that there's nothing to do: maybe
	  ;; because inside a string or something.
	  (if (eq unclosed-comment-fun 'proof-electric-term-incomment-fn)
	    ;; With electric terminator, we shouldn't give an error, but
	    ;; should still insert and pretend it was as if a comment.
	      (proof-electric-term-incomment-fn)
	    (error "I can't find any complete commands to process!"))
	(goto-char (nth 2 (car semis)))
	(and (not ignore-proof-process-p)
	     (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
	       (proof-extend-queue (point) vanillas)))))))


;; da: This is my alternative version of the above.
;; It works from the locked region too.
;; I find it more convenient to assert up to the current command (command
;; point is inside), and move to the next command.
;; This means proofs can be easily replayed with point at the start
;; of lines.  Above function gives stupid "nothing to do error." when
;; point is on the start of line or in the locked region.

;; FIXME: behaviour inside comments may be odd at the moment.  (it
;; doesn't behave as docstring suggests, same prob as
;; proof-assert-until-point)
;; FIXME: polish the undo behaviour and quit behaviour of this
;; command (should inhibit quit somewhere or other).


  
(defun proof-assert-next-command
  (&optional unclosed-comment-fun ignore-proof-process-p
	     dont-move-forward for-new-command)
  "Process until the end of the next unprocessed command after point.
If inside a comment, just process until the start of the comment.  

If you want something different, put it inside UNCLOSED-COMMENT-FUN. 
If IGNORE-PROOF-PROCESS-P is set, no commands will be added to the queue.
Afterwards, move forward to near the next command afterwards, unless
DONT-MOVE-FORWARD is non-nil.  If FOR-NEW-COMMAND is non-nil,
a space or newline will be inserted automatically."
  (interactive)
  (unless ignore-proof-process-p
    (proof-activate-scripting nil 'advancing))
  (or ignore-proof-process-p
      (if (proof-locked-region-full-p)
	  (error "Locked region is full, no more commands to do!")))
  (let ((semis))
    (save-excursion
      ;; CHANGE from old proof-assert-until-point: don't bother check
      ;; for non-whitespace between locked region and point.
      ;; CHANGE: ask proof-segment-up-to to scan until command end
      ;; (which it used to do anyway, except in the case of a comment)
      (setq semis (proof-segment-up-to (point) t)))
    ;; old code:
    ;;(if (not (re-search-backward "\\S-" (proof-unprocessed-begin) t))
    ;;	  (progn (goto-char pt)
    ;;       (error "I don't know what I should be doing in this buffer!")))
    ;; (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car-safe semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car-safe semis))
	  (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (null semis))
	  (error "I can't see any complete commands to process!"))
      (if (nth 2 (car semis))
	  (goto-char (nth 2 (car semis))))
      (if (not ignore-proof-process-p)
	  (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
	    (proof-extend-queue (point) vanillas)))
      ;; This is done after the queuing to be polite: it means the
      ;; spacing policy enforced here is not put into the locked
      ;; region so the user can re-edit.
      (if (not dont-move-forward)
	  (if for-new-command
	      (proof-script-new-command-advance)
	    (proof-script-next-command-advance))))))

(defun proof-goto-point ()
  "Assert or retract to the command at current position.
Calls proof-assert-until-point or proof-retract-until-point as
appropriate."
  (interactive)
  (if (<= (proof-queue-or-locked-end) (point))
      ;; This asserts only until the next command before point and
      ;; does nothing if whitespace between point and locked region.
      (proof-assert-until-point)
    (proof-retract-until-point)))

      
;;         insert-pbp-command - an advancing command, for use when  ;;
;;         PbpHyp or Pbp has executed in LEGO, and returned a       ;;
;;         command for us to run                                    ;;

(defun proof-insert-pbp-command (cmd)
  (proof-activate-scripting)
  (let (span)
    (proof-goto-end-of-locked)
    (insert cmd)
    (setq span (make-span (proof-locked-end) (point)))
    (set-span-property span 'type 'pbp)
    (set-span-property span 'cmd cmd)
    (proof-start-queue (proof-unprocessed-begin) (point) 
		       (list (list span cmd 'proof-done-advancing)))))


;;         proof-retract-until-point and associated gunk            ;;
;;         most of the hard work (i.e computing the commands to do  ;;
;;         the retraction) is implemented in the customisation      ;;
;;         module (lego.el or coq.el) which is why this looks so    ;;
;;         straightforward                                          ;;


(defun proof-done-retracting (span)
  "Callback for proof-retract-until-point.
We update display after proof process has reset its state.
See also the documentation for `proof-retract-until-point'.
Optionally delete the region corresponding to the proof sequence.
After an undo, we clear the proof completed flag.  The rationale
is that undoing never leaves prover in a \"proof just completed\" 
state, which is true for some proof assistants (but probably not
others)."
  (setq proof-shell-proof-completed nil)
  (if (span-live-p span)
      (let ((start (span-start span))
	    (end (span-end span))
	    (kill (span-property span 'delete-me)))
	;; FIXME: why is this test for an empty locked region here?
	;; seems it could prevent the queue and locked regions
 	;; from being detached.  Not sure where they are supposed
 	;; to be detached from buffer, but following calls would
 	;; do the trick if necessary.
	(unless (proof-locked-region-empty-p)
	  (proof-set-locked-end start)
	  (proof-set-queue-end start))
	(delete-spans start end 'type)
	(delete-span span)
	(if kill (kill-region start end))))
  ;; State of scripting may have changed now
  (run-hooks 'proof-state-change-hook))

(defun proof-setup-retract-action (start end proof-command delete-region)
  (let ((span (make-span start end)))
    (set-span-property span 'delete-me delete-region)
    (list (list span proof-command 'proof-done-retracting))))


(defun proof-last-goal-or-goalsave ()
  (save-excursion
    (let ((span (span-at-before (proof-locked-end) 'type)))
    (while (and span 
		(not (eq (span-property span 'type) 'proof))
		(or (eq (span-property span 'type) 'comment)
		    (not (funcall proof-goal-command-p
				  (span-property span 'cmd)))))
      (setq span (prev-span span 'type)))
    span)))

(defun proof-retract-target (target delete-region)
  "Retract the span TARGET and delete it if DELETE-REGION is non-nil.
Notice that this necessitates retracting any spans following TARGET,
up to the end of the locked region."
  (let ((end   (proof-unprocessed-begin))
	(start (span-start target))
	(span  (proof-last-goal-or-goalsave))
	actions)

    ;; Examine the last span in the locked region.  
    
    ;; If the last goal or save span is not a proof or
    ;; prover processed file, we examine to see how to remove it
    (if (and span (not (or
			(memq (span-property span 'type) 
			      '(proof proverproc)))))
	;; If the goal or goalsave span ends before the target span,
	;; then we are retracting within the last unclosed proof,
	;; and the retraction just amounts to a number of undo
	;; steps.  
	;; FIXME: really, there shouldn't be more work to do: so
	;;  why call proof-find-and-forget-fn later?
	(if (< (span-end span) (span-end target))
	    (progn
	      ;; Skip comment spans at and immediately following target
	      (setq span target)
	      (while (and span (eq (span-property span 'type) 'comment))
		(setq span (next-span span 'type)))
	      ;; Calculate undos for the current open segment
	      ;; of proof commands
	      (setq actions (proof-setup-retract-action
			     start end 
			     (if (null span) proof-no-command
			       (funcall proof-count-undos-fn span))
			     delete-region)
		    end start))
	  ;; Otherwise, start the retraction by killing off the
	  ;; currently active goal.
	  ;; FIXME: and couldn't we move the end upwards?
	  (setq actions 
		(proof-setup-retract-action (span-start span) end
					    proof-kill-goal-command
						    delete-region)
		end (span-start span))))
    ;; Check the start of the target span lies before the end
    ;; of the locked region (should always be true since we don't
    ;; make spans outside the locked region at the moment)...
    (if (> end start) 
	(setq actions
	      ;; Append a retract action to clear the entire
	      ;; start-end region.  Rely on proof-find-and-forget-fn
	      ;; to calculate a command which "forgets" back to
	      ;; the first definition, declaration, or whatever
	      ;; that comes after the target span.
	      ;; FIXME: originally this assumed a linear context, 
	      ;; and that forgetting the first thing  forgets all 
	      ;; subsequent ones.  it might be more general to 
	      ;; allow *several* commands, and even queue these
	      ;; separately for each of the spans following target
	      ;; which are concerned.
	      (nconc actions (proof-setup-retract-action 
			      start end
			      (funcall proof-find-and-forget-fn target)
			      delete-region))))
      
    (proof-start-queue (min start end) (proof-locked-end) actions)))

;; FIXME da:  I would rather that this function moved point to
;; the start of the region retracted?

;; FIXME da: Maybe retraction to the start of
;; a file should remove it from the list of included files?
;; NB: the "interactive" variant is so that we get a simple docstring.
(defun proof-retract-until-point-interactive (&optional delete-region)
  "Tell the proof process to retract until point.
If invoked outside a locked region, undo the last successfully processed
command.  If called with a prefix argument (DELETE-REGION non-nil), also
delete the retracted region from the proof-script."
  (interactive "P")
  (proof-retract-until-point delete-region))

(defun proof-retract-until-point (&optional delete-region)
  "Set up the proof process for retracting until point.
In particular, set a flag for the filter process to call 
`proof-done-retracting' after the proof process has successfully 
reset its state.
If DELETE-REGION is non-nil, delete the region in the proof script
corresponding to the proof command sequence.
If invoked outside a locked region, undo the last successfully processed
command."
  ;; Make sure we're ready
  ;; FIXME: next step in extend regions: (proof-activate-scripting nil 'retracting)
  (proof-activate-scripting)
  (let ((span (span-at (point) 'type)))
    ;; FIXME da: shouldn't this test be earlier??
    (if (proof-locked-region-empty-p)
	(error "No locked region"))
    ;; FIXME da: rationalize this: it retracts the last span
    ;; in the buffer if there was no span at point, right?
    ;; why?
    (and (null span)
	 (progn 
	   (proof-goto-end-of-locked) 
	   (backward-char)
	   (setq span (span-at (point) 'type))))
    (proof-retract-target span delete-region)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Restarting and clearing spans 
;;

(defun proof-restart-buffers (buffers)
  "Remove all extents in BUFFERS and maybe reset `proof-script-buffer'.
No effect on a buffer which is nil or killed.  If one of the buffers
is the current scripting buffer, then proof-script-buffer 
will deactivated."
  (mapcar
   (lambda (buffer)
     (save-excursion
       (if (buffer-live-p buffer)
	   (with-current-buffer buffer
	     (if proof-active-buffer-fake-minor-mode
		 (setq proof-active-buffer-fake-minor-mode nil))
	     (delete-spans (point-min) (point-max) 'type) ;; remove spans
	     (setq pg-script-portions nil)		  ;; also the record of them
	     (proof-detach-segments buffer)		  ;; detach queue and locked 
	     (proof-init-segmentation)))
       (if (eq buffer proof-script-buffer)
	   (setq proof-script-buffer nil))))
   buffers))

(defun proof-script-buffers-with-spans ()
  "Return a list of all buffers with spans.
This is calculated by finding all the buffers with a non-nil
value of proof-locked span."
  (let ((bufs-left (buffer-list)) 
	bufs-got)
    (dolist (buf bufs-left bufs-got)
      (if (with-current-buffer buf proof-locked-span)
	  (setq bufs-got (cons buf bufs-got))))))

(defun proof-script-remove-all-spans-and-deactivate ()
  "Remove all spans from scripting buffers via proof-restart-buffers."
  (proof-restart-buffers (proof-script-buffers-with-spans)))

(defun proof-script-clear-queue-spans ()
  "If there is an active scripting buffer, remove the queue span from it.
This is a subroutine used in proof-shell-handle-{error,interrupt}."
  (if proof-script-buffer
      (with-current-buffer proof-script-buffer
	(proof-detach-queue)
	;; FIXME da: point-max seems a bit excessive here,
	;; proof-queue-or-locked-end should be enough.
	(delete-spans (proof-locked-end) (point-max) 'type))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Proof General scripting mode definition, part 1.
;;

(eval-and-compile			; to define vars
;;; NB: autoload tag below doesn't work for d-d-m, autoload is in proof.el
;;;###autoload
(define-derived-mode proof-mode fundamental-mode 
  proof-general-name
  "Proof General major mode class for proof scripts.
\\{proof-mode-map}"

  (setq proof-buffer-type 'script)

  ;; During write-file it can happen that we re-set the mode for
  ;; the currently active scripting buffer.  The user might also
  ;; do this for some reason.  We could maybe let
  ;; this pass through, but it seems safest to treat it as
  ;; a kill buffer operation (retract and clear spans).
  ;; (NB: other situations seem to cause double successive calls to
  ;; proof-mode).
  (if (eq (current-buffer) proof-script-buffer)
      (proof-script-kill-buffer-fn))

  ;; We set hook functions here rather than in proof-config-done so
  ;; that they can be adjusted by prover specific code if need be.
  (proof-script-set-hooks)
  (make-local-hook 'after-set-visited-file-name-hooks)
  (add-hook 'after-set-visited-file-name-hooks 'proof-script-set-visited-file-name)

  (make-local-hook 'proof-activate-scripting-hook)
  (add-hook 'proof-activate-scripting-hook 'proof-cd-sync nil t)))

;; NB: proof-mode-map declared by define-derived-mode above
(proof-menu-define-keys proof-mode-map)

(defun proof-script-set-visited-file-name ()
  "Called when visited file name is changed.

This is a hook function for `after-set-visited-file-name-hooks'.

For some provers, the file from which script commands are being
processed may be important, and if it is changed with C-x C-w, for
example, we might have to retract the contents or inform the proof
assistant of the new name.  This should be done by adding 
additional functions to `after-set-visited-file-name-hooks'.

At the least, we need to set the buffer local hooks again
with `proof-script-set-hooks' which is what this function does.
It also gives a warning in case this is the active scripting buffer."
  (if (eq (current-buffer) proof-script-buffer)
      (proof-warning "Active scripting buffer changed name; synchronization risked if prover tracks filenames!"))
  (proof-script-set-hooks))

(defun proof-script-set-hooks ()
  "Set the hooks for a proof script buffer.
The hooks set here are cleared by write-file, so we use this function
to restore them using `after-set-visited-file-name-hooks'."
  (make-local-hook 'kill-buffer-hook)
  (add-hook 'kill-buffer-hook 'proof-script-kill-buffer-fn t t)
  ;; Reverting buffer is same as killing it as far as PG is concerned
  (make-local-hook 'before-revert-hook)
  (add-hook 'before-revert-hook 'proof-script-kill-buffer-fn t t))
  
(defun proof-script-kill-buffer-fn ()
  "Value of kill-buffer-hook for proof script buffers.
Clean up before a script buffer is killed.
If killing the active scripting buffer, run proof-deactivate-scripting.
Otherwise just do proof-restart-buffers to delete some spans from memory."
  ;; Deactivate scripting in the current buffer if need be, forcing
  ;; automatic retraction if the buffer is not fully processed.
  (unwind-protect
      (if (eq (current-buffer) proof-script-buffer)
	  (proof-deactivate-scripting 'retract))
    (proof-restart-buffers (list (current-buffer)))
    ;; Hide away goals and response: this is a hack because otherwise
    ;; we can lead the user to frustration with the dedicated windows
    ;; nonsense.
    (if (buffer-live-p proof-goals-buffer) 
	(bury-buffer proof-goals-buffer))
    (if (buffer-live-p proof-response-buffer)
	(bury-buffer proof-response-buffer))))


;; Notes about how to deal with killing/reverting/renaming buffers:
;; (As of XEmacs 21.1.9, see files.el)
;;
;; Killing: easy, set kill-buffer-hook
;; Reverting: ditto, set before-revert-hook to do same as kill.
;; Renaming (write-file): much tricker.  Code for write-file does
;;  several odd things.  It kills off local hook functions, calls
;;  `after-set-visited-file-name-hooks' right at the end to give the
;;  chance to restore them, but then tends to automatically (re-)set
;;  the mode anyway.
  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  Proof General scripting mode definition - part 2
;; 

;; The functions proof-config-done[-related] are called after the
;; derived mode has made its settings.

;; The callback *-config-done mechanism is an irritating hack - there
;; should be some elegant mechanism for computing constants after the
;; child has configured.  Should petition the author of "derived-mode"
;; about this!

(defun proof-config-done-related ()
  "Finish setup of Proof General scripting and related modes.
This is a subroutine of proof-config-done.

This is intended for proof assistant buffers which are similar to
script buffers, but for which scripting is not enabled.  In
particular, we: lock the buffer if it appears on
proof-included-files-list; configure font-lock support from
font-lock-keywords; maybe turn on X-Symbol minor mode.

This is used for Isabelle theory files, which share some scripting 
mode features, but are only ever processed atomically by the proof
assistant."
  ;; Has buffer already been processed?
  ;; NB: call to file-truename is needed for FSF Emacs which
  ;; chooses to make buffer-file-truename abbreviate-file-name
  ;; form of file-truename.
  (and buffer-file-truename
       (member (file-truename buffer-file-truename)
	       proof-included-files-list)
       (proof-complete-buffer-atomic (current-buffer)))

  ;; calculate some strings and regexps for searching
  (setq proof-terminal-string 
	(if proof-terminal-char
	    (char-to-string proof-terminal-char)
	  ""))

  (make-local-variable 'comment-start)
  (setq comment-start (concat proof-comment-start " "))
  (make-local-variable 'comment-end)
  (setq comment-end (concat " " proof-comment-end))
  
  (unless proof-comment-start-regexp
    (setq proof-comment-start-regexp (regexp-quote proof-comment-start)))
  (unless proof-comment-end-regexp
    (setq proof-comment-end-regexp (regexp-quote proof-comment-end)))

  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip 
    (concat proof-comment-start-regexp "+\\s_?"))

  ;;
  ;; Fontlock support.
  ;;
  ;; Assume font-lock case folding follows proof-case-fold-search
  (proof-font-lock-configure-defaults proof-case-fold-search)
  
  ;; Hack for unfontifying commas (yuck)
  (remove-hook 'font-lock-after-fontify-buffer-hook 'proof-zap-commas-buffer t)
  (remove-hook 'font-lock-mode-hook 'proof-unfontify-separator t)
  (if proof-font-lock-zap-commas
      (progn
	(add-hook 'font-lock-after-fontify-buffer-hook 
		  'proof-zap-commas-buffer nil t)
	(add-hook 'font-lock-mode-hook 'proof-unfontify-separator 
		  nil t)
	;; if we don't have the following in XEmacs, zap-commas fails.
	(if (boundp 'font-lock-always-fontify-immediately)
	    (progn
	      (make-local-variable 'font-lock-always-fontify-immediately)
	      ;; FIXME da: this is pretty nasty.  Disables use of 
	      ;; lazy/caching font lock for large files, and they
	      ;; can take a long time to fontify.
	      (setq font-lock-always-fontify-immediately t)))))

  ;; Maybe turn on x-symbol mode.
  (proof-x-symbol-mode))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic defaults for hooks, based on regexps.
;; 
;; NEW November 1999.  
;; Added to PG 3.0 but only used for demoisa so far.
;;

;;
;; FIXME: the next step is to use proof-stringfn-match scheme more
;; widely, to allow settings which are string or fn, so we don't need
;; both regexp and function hooks, and so that the other hooks can be
;; functions too.
;;

(defun proof-generic-goal-command-p (str)
  "Is STR a goal?  Decide by matching with proof-goal-command-regexp."
  (proof-string-match-safe proof-goal-command-regexp str))

(defun proof-generic-state-preserving-p (cmd)
  "Is CMD state preserving?  Match on proof-non-undoables-regexp."
  (not (proof-string-match-safe proof-non-undoables-regexp cmd)))

(defun proof-generic-count-undos (span)
  "Count number of undos in a span, return command needed to undo that far.
Command is set using `proof-undo-n-times-cmd'.

A default value for `proof-count-undos-fn'.

For this function to work properly, you must configure
`proof-undo-n-times-cmd' and `proof-ignore-for-undo-count'."
  (let
      ((case-fold-search proof-case-fold-search)
       (ct 0) str i)
    (while span
      (setq str (span-property span 'cmd))
      (cond ((eq (span-property span 'type) 'vanilla)
	     (unless (proof-stringfn-match proof-ignore-for-undo-count str)
	       (incf ct)))
	    ((eq (span-property span 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length str)) 
	       (if (= (aref str i) proof-terminal-char) (incf ct))
	       (incf i))))
      (setq span (next-span span 'type)))
    (if (= ct 0)
	proof-no-command
      (cond ((stringp proof-undo-n-times-cmd)
	     (format proof-undo-n-times-cmd ct))
	    ((functionp proof-undo-n-times-cmd)
	     (funcall proof-undo-n-times-cmd ct))))))

(defun proof-generic-find-and-forget (span)
  "Calculate a forget/undo command to forget back to SPAN.
This is a long-range forget: we know that there is no
open goal at the moment, so forgetting involves unbinding
declarations, etc, rather than undoing proof steps.

Currently this has a trivial implementation: it 
just returns proof-no-command, meaning `do nothing'.

Check the lego-find-and-forget or coq-find-and-forget
functions for examples of how to write this function."
  ;; FIXME: implement a useful generic find-and-forget
  proof-no-command)

;;
;; End of new generic functions
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;
;; Sanity checks on important settings
;;

(defconst proof-script-important-settings
  '(proof-comment-start			;
    proof-comment-end
    ; proof-goal-command-regexp	  not needed if proof-goal-command-p is set
    proof-save-command-regexp
;    proof-goal-with-hole-regexp		; non-essential?
;    proof-save-with-hole-regexp		; non-essential?
    proof-showproof-command		; non-essential?
    proof-goal-command			; non-essential
    proof-save-command			; do
    proof-kill-goal-command		; do
    ))

(defun proof-config-done () 
  "Finish setup of Proof General scripting mode.
Call this function in the derived mode for the proof assistant to
finish setup which depends on specific proof assistant configuration."

  (proof-config-done-related)

  ;; Following group of settings only relevant if the current
  ;; buffer is really a scripting buffer.  Isabelle Proof General
  ;; has theory file buffers which share some aspects, they
  ;; just use proof-config-done-related.

  ;; Preamble: make this mode class "pg-sticky" so that renaming file
  ;; to something different doesn't change the mode, no matter what
  ;; the filename.  This is a hack so that write-file will work:
  ;; otherwise Emacs insists (as of XEmacs 21.1.9 at least) on
  ;; re-setting the mode, which leads to problems with synchronization
  ;; and losing extents.  (Attempt to catch this in proof-mode by
  ;; looking for active scripting buffer fails; perhaps because of
  ;; kill buffer function)
  (put major-mode 'mode-class 'pg-sticky)

  ;; First, define some values if they aren't defined already.
  (unless proof-mode-for-script
      (setq proof-mode-for-script major-mode))

  (if (and proof-non-undoables-regexp 
	   (not proof-ignore-for-undo-count))
      (setq proof-ignore-for-undo-count 
	    proof-non-undoables-regexp))

  ;; Give warnings if some crucial settings haven't been made
  (dolist (sym proof-script-important-settings)
    (proof-warn-if-unset "proof-config-done" sym))

  ;; Additional key definitions which depend on configuration for
  ;; specific proof assistant.
  ;; FIXME da: generalize here.  Might have electric terminator for
  ;; other parsing mechanisms too, using new proof-script-parse-function
  ;; Could use a default terminal char
  (if proof-terminal-char
      (progn
	(define-key proof-mode-map
	  (vconcat [(control c)] (vector proof-terminal-char))
	  'proof-electric-terminator-toggle)
	(define-key proof-mode-map (vector proof-terminal-char)
	  'proof-electric-terminator)))
  ;; It's ugly, but every script buffer has a local copy changed in
  ;; sync by the fn proof-electric-terminator-enable 
  (setq proof-electric-terminator proof-electric-terminator-enable)

  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'proof-indent-line)

  ;; Toolbar and scripting menu
  ;; NB: autloads proof-toolbar, which defines proof-toolbar-scripting-menu.
  (proof-toolbar-setup)

  ;; Menus: the Proof-General and the specific menu
  (proof-menu-define-main)
  (proof-menu-define-specific)
  (easy-menu-add proof-mode-menu proof-mode-map)
  (easy-menu-add proof-assistant-menu proof-mode-map)

  ;; Choose parsing mechanism according to different kinds of script syntax.  
  ;; Choice of function depends on configuration setting.
  (unless (fboundp 'proof-segment-up-to)
    (if (or proof-script-use-new-parser
	    proof-script-sexp-commands)
	;; 3.3 mechanism here
	(progn
	  (defalias 'proof-segment-up-to 'proof-segment-up-to-parser)
	  (cond   
	   (proof-script-parse-function
	    ;; already set, nothing to do
	    )
	   (proof-script-sexp-commands
	    (setq proof-script-parse-function 'proof-script-generic-parse-sexp))
	   (proof-script-command-start-regexp
	    (setq proof-script-parse-function 'proof-script-generic-parse-cmdstart))
	   ((or proof-script-command-end-regexp proof-terminal-char)
	    (setq  proof-script-parse-function 'proof-script-generic-parse-cmdend)
	    (unless proof-script-command-end-regexp
	      (proof-warn-if-unset "proof-config-done" 'proof-terminal-char)
	      (setq proof-script-command-end-regexp
		    (if proof-terminal-char
			(regexp-quote (char-to-string proof-terminal-char))
		      "$"))))
	   (t
	    (error "Configuration error: must set `proof-terminal-char' or one of its friends."))))
      (cond
       (proof-script-parse-function	;; still allowed to override in 3.2
	(defalias 'proof-segment-up-to 'proof-segment-up-to-parser))
       ;; 3.2 mechanism here
       (proof-script-command-start-regexp
	(defalias 'proof-segment-up-to 'proof-segment-up-to-cmdstart))
       (t
	(defalias 'proof-segment-up-to 'proof-segment-up-to-cmdend)
	(unless proof-script-command-end-regexp
	  (proof-warn-if-unset "proof-config-done" 'proof-terminal-char)
	  (setq proof-script-command-end-regexp
		(if proof-terminal-char
		    (regexp-quote (char-to-string proof-terminal-char))
		  "$"))))))) ;  default if nothing set is EOL.

  ;; Make sure func menu is configured.  (NB: Ideal place for this and
  ;; similar stuff would be in something evaluated at top level after
  ;; defining the derived mode: normally we wouldn't repeat this
  ;; each time the mode function is run, so we wouldn't need "pushnew").

  (cond ((proof-try-require 'func-menu)
	 ;; FIXME: we'd like to let the library load later, but 
	 ;; it's a bit tricky: this stuff doesn't seem to work
	 ;; in an eval-after-load body (local vars?).
	 (unless proof-script-next-entity-regexps ; unless already set
	   ;; Try to calculate a useful default value.
	   ;; FIXME: this is rather complicated!  The use of the regexp
	   ;; variables needs sorting out. 
	     (customize-set-variable
	      'proof-script-next-entity-regexps
	      (let ((goal-discrim
		     ;; Goal discriminator searches forward for matching
		     ;; save if the regexp is set.
		     (if proof-goal-with-hole-regexp
			 (if proof-save-command-regexp
			     (list
			      proof-goal-with-hole-regexp 2
			      'forward proof-save-command-regexp)
			   (list proof-goal-with-hole-regexp 2))))
		    ;; Save discriminator searches backward for matching
		    ;; goal if the regexp is set.
		    (save-discrim
		     (if proof-save-with-hole-regexp
			 (if proof-goal-command-regexp
			     (list
			      proof-save-with-hole-regexp 2
			      'backward proof-goal-command-regexp)
			   (list proof-save-with-hole-regexp 2)))))
		(cond
		 ((and proof-goal-with-hole-regexp proof-save-with-hole-regexp)
		  (list
		   (proof-regexp-alt
		    proof-goal-with-hole-regexp
		    proof-save-with-hole-regexp) goal-discrim save-discrim))
		  
		 (proof-goal-with-hole-regexp
		  (list proof-goal-with-hole-regexp goal-discrim))
		 
		 (proof-save-with-hole-regexp
		  (list proof-save-with-hole-regexp save-discrim))))))

	 (if proof-script-next-entity-regexps
	     ;; Enable func-menu for this mode if regexps set now
	     (progn
	       (pushnew
		(cons major-mode 'proof-script-next-entity-regexps)
		fume-function-name-regexp-alist)
	       (pushnew
		(cons major-mode proof-script-find-next-entity-fn)
		fume-find-function-name-method-alist)))))

  ;; Offer to save script mode buffers which have no files,
  ;; in case Emacs is exited accidently.
  (or (buffer-file-name)
      (setq buffer-offer-save t))

  ;; To begin with, make everything visible in the buffer
  (setq buffer-invisibility-spec nil)

  ;; Finally, make sure the user has been welcomed!
  ;; FIXME: this doesn't work well, it gets zapped by loading messages.
  (proof-splash-message))


(provide 'proof-script)
;; proof-script.el ends here.

