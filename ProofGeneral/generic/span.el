;; span.el	Datatype of "spans" for Proof General.
;; Copyright (C) 1998 LFCS Edinburgh
;; Author:	Healfdene Goguen
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; span.el,v 5.0 2000/09/29 19:03:43 da Exp


;; Spans are our abstraction of extents/overlays.
;; 
(eval-and-compile
  (cond
   ((fboundp 'make-extent)    (require 'span-extent))
   ((fboundp 'make-overlay)   (require 'span-overlay))
   (t			       
    (error 
     "Your Emacs version is not compatible with Proof General, sorry."))))

(provide 'span)
;; span.el ends here.
