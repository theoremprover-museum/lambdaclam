# #####################################
# #####################################
#
# DISPLAYING FONTS AND WAVE ANNOTATIONS
#
# #####################################
# #####################################

# proc annotate_widget
#
# This takes a piece of text and a widget and adds entries to an array,
# TagArray, holding information about where in the text wave annotations
# and natural symbols occur. 
#
# The procedure takes as arguments a widget pathname (where the text is
# to be displayed), the type of the widget (canvas or text), a location
# (an indication of whether the text will be displayed in a node in the
# proof tree or elsewhere); the unformatted text to be displayed; and an
# optional startline used for when adding more text to a textbox that
# already has some annotated text.
#
# Given a piece of text from LambdaCLaM's LaTeX trace mode, for example: 
#
# "\(ripGoal\)*\(U_1$ \aleph \)*\(\forall\,V\sb{1} V\sb{0}: \aleph    (((V\sb{1} + V\sb{0}) + U_1) = (V\sb{1} + (V\sb{0} + U_1)))\)*\(\vdash\,(((((U_3\,\, + \,U_2\,)\,\, + \,\wf{s\,\,\wh{U_1}\,}\,)\,\, = \,(U_3\,\, + \,(U_2\,\, + \,\wf{s\,\,\wh{U_1}\,}\,)\,)\,)\,)\,)\)"
#
# annotate_NaturalFont is called to remove redundant detail, convert 
# natural mathematical symbols to a standard four character format
# (XBnn), and, via a call to annotate_WaveAnnotations, to add markers of
# form ~XANN_DEPTH_1 and ~1_DEPTH_ to indicate the bounds of rippling
# annotations (where ANN indicates the type of annotation (of - out
# front, if - in front, wh - hole, si - sink) and DEPTH represents the
# depth of nesting of this annotated term). This would convert the above
# term to:
#
# ripGoal*U_1$ XB03 *XB01 V1 V0: XB03 (((V1 + V0) + U_1) = (V1 + (V0 + U_1)))*XB16 (((((U_3 + U_2 ) +  ~Xof_1_1 s  ~Xwh_2_1 U_1 ~1_2_~   ~1_1_~  ) = (U_3 + (U_2 +  ~Xof_1_1 s  ~Xwh_2_1 U_1 ~1_2_~   ~1_1_~  )) )) )
#
# A version of the above is then produced. This is the text that will
# actually be placed in the given widget. For example:
#
# ripGoal*U_1$ N *" V1 V0: N (((V1 + V0) + U_1) = (V1 + (V0 + U_1)))*|- (((((U_3 + U_2 ) +   s   U_1      ) = (U_3 + (U_2 +   s   U_1      )) )) )
#
# Information in the TagArray can then be used to determine where to add 
# tags to textboxes and how to draw rectangles in canvases to produce
# shaded wave annotations.
#
# For a widget widget we store:
#
# TagArray(widget,depth) - maximum depth of annotation nesting in
#			 - the term displayed in the widget.
# TagArray(widget,term) - the text that will actually be inserted
#			- into the widget.
# TagArray(widget,type) - type of widget (canvas or text).
# TagArray(widget,tagnumber) - number of wave annotations in widget.
# TagArray(widget,syms) - list of (line start end) triples for natural
#                       - symbols - the line upon which a natural
#                       - symbol is to be displayed and the start and
#                       - end positions in this line. 
# TagArray(widget,endline) - for textboxes the number of the last
#		           - line on which text was placed
#
# For each annotation with index ind [0..TagArray(widget,tagnumber)] we
# store:
#
# TagArray(widget,ind,start) - start character position of annotation
# TagArray(widget,ind,depth) - depth of annotation nesting
# TagArray(widget,ind,type) - type of annotation (wave front etc)
# TagArray(widget,ind,stop) - stop character position of annotation

proc annotate_widget {location widgettype widgetpath unformatted {startline 1}} {
global xb TagArray TagWidgets FontCodes
  # TagWidgets holds a list of all widgets that feature contents
  # requiring wave annotations or natural mathematical symbols
  if ![info exists TagWidgets] {
    set TagWidgets [list $widgetpath]
  } else {
    # If startline == 1 then this widget currently has no annotations or 
    # natural fonts in it. In this case add the widget name to
    # TagWidgets 
    if {$startline == 1} {
      set TagWidgets [concat $TagWidgets $widgetpath]
    }
  }
  # Convert all LaTeX markups for mathematical characters and ripple
  # annotations to a standard format.
  set unformatted [annotate_NaturalFont $location $unformatted]
  set conjsize [string length $unformatted]
  # Line is used for textboxes - the current line of the textbox into
  # which the new text is to be placed 
  set line 1
  # cnt is used as an index into a string that holds the text that will
  # actually be inserted into the widget (the text that will be stored
  # in the TagArray(widget,term) entry of TagArray).
  set cnt 0
  # Indcnt is the number of annotations encountered so far
  set indcnt 0
  # j is always equal to the number of annotations encountered so far
  # plus 1 
  set j 0
  # If text is being added to existing widget and that widget has not
  # previously been wiped then continue from where we left off. Only
  # applicable to textboxes. 
  if {[info exists TagArray($widgetpath,tagnumber)] && $startline != 1} {
    set indcnt $TagArray($widgetpath,tagnumber)
    set j [expr $indcnt + 1]
    set maxdepth $TagArray($widgetpath,depth)
    set line $TagArray($widgetpath,endline)
    incr line
    # Mark that we are inserting additional text into a widget that
    # already has annotations (and hence already has TagArray entries)
    set append 1
  } else {
    # We are dealing with a new widget...
    set TagArray($widgetpath,syms) [list]
    set indcnt -1
    set j 0
    set maxdepth 0
    set append 0
  }
  set TagArray($widgetpath,type) $widgettype
  # nuterm holds the text that will actually be placed in the widget
  # and will be stored in the TagArray(widget,term) entry of TagArray
  set nuterm ""
  # Go through the formatted version of the text a character at a
  # time... 
  for {set i 0} {$i < $conjsize} {incr i} {
    # Get the characters that are at the ith and i+1th positions in
    # the term. 
    set c [string index $unformatted $i]
    set c1 [string index $unformatted [expr $i + 1]]
    # The character ~ is used to indicate that annotation information
    # is present and follows the tilde. If the tilde is present then
    # we retrieve this annotation information.
    if {$c == "~" && $c1 == "X"} {
      # ~X denotes we are in scope of start-of-annotation marker of
      # form ~XANN_DEPTH_1 where ANN = of (out); if (in); wh (hole);
      # si (sink), DEPTH is the depth of nesting of the annotation in
      # its enclosing annotations.
      # Set i to point at the annotation type...
      incr i
      incr i
      # Get the annotation type from the string
      set col [string range $unformatted $i [expr $i + 1]]
      incr i
      # Set i to point at the first character of the sub-string holding
      # the depth of nesting of this annotation
      incr i
      incr i
      # Get the depth of nesting of this annotation
      set depthindex [annotate_depth $unformatted $i]
      # Update the index into the text being traversed
      set i [lindex $depthindex 1]
      # Set i to point at the trailing 1 of the annotation markup
      incr i
      # Check that i is now pointing at the last part of the
      # start-of-annotation marker (i.e. the 1)
      set c [string index $unformatted $i]
      if {$c == "1"} {
        # Increase count of annotations encountered
        incr indcnt
        # If the nesting depth of this annotation is larger than any
        # already encountered then update maxdepth
        if {[lindex $depthindex 0] > $maxdepth} {
          set maxdepth [lindex $depthindex 0]
        }
        # For textboxes store the line and the position within the line
        # at which the annotation starts. For canvases just store the
        # character position in a line.
        if {$widgettype == "text"} {
          set TagArray($widgetpath,$indcnt,start) $line.$cnt
        } else {
          set TagArray($widgetpath,$indcnt,start) $cnt
        }
        # Store depth of nesting of this annotation
        set TagArray($widgetpath,$indcnt,depth) [lindex $depthindex 0]
        # Store the type of this annotation (i.e. of, if, wh, or si) 
        set TagArray($widgetpath,$indcnt,type) $col
        # This annotation is the $indcnt-th one we have encountered. We
	# save this number in the array anno indexed by the depth of
	# this annotation. This is so we can retrieve this annotation
	# number using the depth when we exit the annotation scope.
        set anno([lindex $depthindex 0]) $indcnt
      }	
    } elseif {$c == "~"} {
      # We are in the scope of an end-of-annotation marker of form
      # ~1_ANNDEPTH_ 
      incr i 
      set c [string index $unformatted $i]
      # Set index into string to point at the DEPTH fragment
      incr i
      incr i
      # Get the depth of nesting of this annotation
      set depthindex [annotate_depth $unformatted $i]
      # Update the index into the string to point at the _ after the
      # DEPTH fragment
      set i [lindex $depthindex 1]
      incr i
      # Check that i is now pointing at the last part of the
      # start-of-annotation marker (i.e. the 1)
      if {$c == "1"} {				        
        # The entry of array anno that is indexed by the depth we have 
	# retrieved will contain the number of the annotation that this
	# end-of-annotation marker is closing off. We then save in
	# TagArray information indicating the end position of this
	# annotation in the term.
        if {$widgettype == "text"} {
          set TagArray($widgetpath,$anno([lindex $depthindex 0]),stop) \
            $line.$cnt
        } else {
          set TagArray($widgetpath,$anno([lindex $depthindex 0]),stop) \
           $cnt
        }
      }
    } else {
      # We have not encountered an annotation marker
      set c2 [string index $unformatted [expr $i + 1]]
      set code1 [string index $unformatted [expr $i + 2]]
      # Check if we are encountering a natural symbol marker (of form
      # XBnn) 
      if {$c == "X" && $c2 == "B" && ( $code1 == "0" || $code1 == "1") } {
        # We have encountered a natural symbol marker of form XBnn
        set code2 [string index $unformatted [expr $i + 3]]
        set code $code1$code2
        # Get the symbol with which to replace the marker
        set font_code $FontCodes($code)
        set char [lindex $font_code 0]
        set lenf [lindex $font_code 1]
        # Save the line number and start and end positions of this
	# symbol i.e. where it resides in the term nuterm
        set TagArray($widgetpath,syms) \
          [linsert $TagArray($widgetpath,syms) end \
          [list $line $cnt [expr $cnt + $lenf]]]
        # Add the symbol to nuterm
        set nuterm $nuterm$char
        # Update the index into the term being traversed
        set i [expr $i + 3]
        set cnt [expr $cnt + $lenf]
      } else {
        # Just an ordinary character so add the character to nuterm
        set nuterm $nuterm$c
        if {$c == "\n"} {
          incr line
          if {$widgettype == "text"} {
            # Start of new line in textbox 
            set cnt 0
          } else {
            # Ignore new line in canvas
            incr cnt
          }
        } else {
          incr cnt
        }
      }
    }
  }
  # Store the number of wave annotations that are now present in the
  # widget, the maximum depth to which these annotations are nested
  # and the index of the last line into which text was inserted
  set TagArray($widgetpath,tagnumber) $indcnt
  set TagArray($widgetpath,depth) $maxdepth
  set TagArray($widgetpath,endline) $line
  # Save the actual text to be inserted into the widget
  # If adding text to existing text then add a \n so that the new text
  # is on a new line
  if {$append} {
    set TagArray($widgetpath,term) "\n$nuterm"
  } else {
    set TagArray($widgetpath,term) $nuterm
  }
  return $line
}

# proc annotate_text_widget
#
# widgetpath holds a pathname of a textbox widget. unformatted holds a
# piece of text that must be placed in the textbox - this text may contain 
# LaTeX markups which must be processed so that the text, when placed in
# the textbox, uses natural fonts and displays rippling annotations in a 
# shaded manner. Startline holds an optional index indicating at which
# line in the textbox the text is to be inserted. Location specifies if
# the textbox is being used as part of a node in the proof tree or not.

proc annotate_text_widget {location widgetpath unformatted {startline 1}} {
global xb TagArray colours
  # Process the unformatted term (so it can support the display of
  # natural fonts) and build TagArray entries for the textbox which hold 
  # information about the start and end locations of wave annotations
  # and characters to be displayed in natural fonts.
  annotate_widget $location text $widgetpath $unformatted $startline
  # Configure the textbox so that a tag called symbolo can be added -
  # this use of tags allows one textbox to feature characters from two
  # separate fonts and so allows the incorporation of mathematical
  # symbols with ordinary text
  $widgetpath tag configure symbolo -font $xb(fontmaths10)
  # Insert the processed version of the unformatted term into the
  # textbox.
  $widgetpath insert end $TagArray($widgetpath,term)
  # For every character in the term to be displayed using a natural
  # font...
  foreach naturalfont $TagArray($widgetpath,syms) {
    # Find the line that the character lies on and the start and end
    # positions of the character on this line
    set line [lindex $naturalfont 0]
    set start [lindex $naturalfont 1]
    set finish [lindex $naturalfont 2]
    # Add the symbolo tag so that it spans the extent of this character
    $widgetpath tag add symbolo $line.$start end
    $widgetpath tag remove symbolo $line.$finish end
  } 
  # For every annotation in the term...
  for {set i 0} {$i <= $TagArray($widgetpath,tagnumber)} {incr i} {
    # Add a new tag with index i spanning the extent of the annotation
    $widgetpath tag add $i $TagArray($widgetpath,$i,start) \
      $TagArray($widgetpath,$i,stop)
    # Set the colours of this tag
    $widgetpath tag configure $i -foreground \
      $colours($TagArray($widgetpath,$i,type),fore) \
      -background $colours($TagArray($widgetpath,$i,type),back)
  }
  annotate_show_annotations
}

# proc annotate_canvas_widget
#
# widgetpath holds a pathname of a canvas widget. unformatted holds a
# piece of text that must be placed in the canvas - this text may
# contain LaTeX markups which must be processed so that the text, when
# placed on the canvas, uses natural fonts and displays rippling
# annotations in a box-and-hole manner. 

proc annotate_canvas_widget {widgetpath unformatted} {
global xb TagArray colours
  # Process the unformatted term (so it can support the display of
  # natural fonts) and build TagArray entries for the canvas which hold 
  # information about the start and end locations of wave annotations
  # and characters to be displayed in natural fonts.
  annotate_widget node canvas $widgetpath $unformatted 1
  # Number of pixels between letters
  set letter_gap 7
  set lenf [string length $TagArray($widgetpath,term)]
  # X and Y coordinates of where the text is to be placed in the canvas
  set base_x 20
  set base_y 60
  set syms $TagArray($widgetpath,syms)
  set natural_font_scope 0
  # actual_x stores the x coordinate on the display where a character
  # will be displayed. This will be reset to zero each time we encounter
  # a newline marker "*"  
  set actual_x -1
  # last_nl is used to get the index of the string at which the last
  # newline of the string is encountered. This is so that wave
  # annotation rectangles can be drawn correctly.
  set last_nl 0
  set lines 1
  # -i is the character in the processed version of the term, stored in
  # the TagArray, that we are displaying in the canvas
  # Go through the string to be inserted into the canvas
  for {set i 0} {$i < $lenf} {incr i} {
    incr actual_x
    # Get the position of the first symbol to be displayed in a natural
    # font
    set symtop [lindex $syms 0]
    # Is our index into the term pointing to a symbol to be displayed in 
    # a natural font ?
    if {[lindex $symtop 1] == $i} {
      # The letter must be rendered via the mathematical font
      # Put the character onto the canvas using mathematical font - give 
      # it a tag lett$i
      $widgetpath create text \
        [expr $base_x + ($letter_gap * $actual_x)] $base_y \
        -anchor center -text [string index $TagArray($widgetpath,term) \
        $i] -font $xb(fontmaths10) -tag lett$i
      set nfstart [lindex $symtop 1]
      set nffinish [lindex $symtop 2]
      # This is used for cases where two or more characters are used to
      # represent a symbol in a "natural" form (e.g. <> or ::). We use
      # natural_font_scope to keep track of how many characters we need
      # to display in a natural font. Such cases are caught by the
      # second-branch of the main if, just below...
      set natural_font_scope [expr $nffinish - $nfstart - 1]
      # Remove the information about the natural symbol displayed from
      # syms
      set syms [lrange $syms 1 end]
    } elseif {$natural_font_scope != 0} {
      # Then need to display this using the mathematical font
      $widgetpath create text [expr $base_x + ($letter_gap \
        * $actual_x)] $base_y -anchor center -text [string index \
        $TagArray($widgetpath,term) $i] -font $xb(fontmaths10) -tag \
        lett$i 
      set natural_font_scope [expr $natural_font_scope - 1]
    } elseif {[string index $TagArray($widgetpath,term) $i] == "*"} {
      # A newline marker is encountered so update the y position and the
      # x position, actual_x. Mark the location of this newline in
      # last_nl
      set base_y [expr $base_y + 30]
      set last_nl $i
      set actual_x 0
      incr lines
    } else {
      # Just display the letter
      $widgetpath create text [expr $base_x + ($letter_gap * \
        $actual_x)] $base_y -anchor center -text [string index \
        $TagArray($widgetpath,term) $i] -font $xb(font) -tag lett$i
    } 
    # Find out if the character is within the scope of a wave annotation 
    # and if so find out the type of the immediately enclosing annotation
    # This is so we can set the colour of the letter appropriately
    set encloser [annotate_FindEnclosingAnnotation $widgetpath $i]
    if {$encloser != -1} {
      $widgetpath itemconfigure lett$i -fill \
        $colours($TagArray($widgetpath,$encloser,type),fore)
    }
  }
  # Now draw shaded rectangles for annotations - go through each
  # annotation in turn
  for {set i 0} {$i <= $TagArray($widgetpath,tagnumber)} {incr i} {
    # Find the bounds in the term of the rectangle
    set starting $TagArray($widgetpath,$i,start)
    set stopping $TagArray($widgetpath,$i,stop)
    # Now update these in light of newlines - note that this code at
    # present assumes that any annotated terms will all occur on one
    # line and this will be the last line to be displayed in the canvas
    set starting [expr $starting - $last_nl]
    set stopping [expr $stopping - $last_nl]
    set ygap 10
    # We use the maximum depth of nesting of annotations to decide how
    # large the rectangles representing the outermost annotations need
    # to be 
    set max_y [expr $ygap + (($TagArray($widgetpath,depth) - \
      $TagArray($widgetpath,$i,depth)) * 2)]
    set min_y [expr $base_y - $max_y]
    set max_y [expr $base_y + $max_y]
    # Each annotation rectangle drawn in a canvas will have tag rect$i
    $widgetpath create rectangle [expr $base_x + ($letter_gap *\
      $starting)] $min_y [expr $base_x + ($letter_gap * $stopping)] \
      $max_y -fill $colours($TagArray($widgetpath,$i,type),back) \
      -outline $colours($TagArray($widgetpath,$i,type),back) -tag rect$i
    $widgetpath raise rect$i
  }
  # Since the rectangles will have been drawn over the text raise the
  # text in the display so that it is displayed above the rectangles 
  for {set i 0} {$i < $lenf} {incr i} {
    $widgetpath raise lett$i
  }
  annotate_show_annotations
}

# proc annotate_FindEnclosingAnnotation
#
# Given a position in a term in a widget and a widget name (which allows
# us to retrieve the term from TagArray) find out if the letter of the
# term specified by index is part of a wave annotation. If so return a
# number that specifies the type of annotation 0 = out front, 1 = in
# front, 2 = hole, 3 = sink.

proc annotate_FindEnclosingAnnotation {path index} {
global TagArray
  set encloser -1
  for {set j 0} {$j <= $TagArray($path,tagnumber)} {incr j} {
    set starting $TagArray($path,$j,start)
    set stopping $TagArray($path,$j,stop)
    # If the index lies between the start and stop bounds of an
    # annotation then we have found the enclosing annotation. Since we
    # go through every annotation in the for loop and since in a group
    # of nested annotations the most nested annotation will have the
    # highest tag number this is guaranteed to return the type of the
    # annotation that most directly encloses the letter
    if {($starting <= $index) && ($stopping > $index) } {
      set encloser $j
    }
  }
  return $encloser
}

# proc annotate_depth
#
# This procedure is used when we encounter markups denoting the entry or 
# exit of an annotation (i.e. ~XANN_DEPTH_1 or ~1_DEPTH_) and assumes
# that the prefixes to the DEPTH (i.e. ~XANN_ or ~1_) have already been 
# stripped off - denoted by the variable index which will point into the 
# string at the first character of the DEPTH fragment.
#
# This procedure will strip off the characters in the DEPTH part of the
# markup and convert these to the appropriate integer. For example if
# the string is "~testXwf_123_1test" with index pointing to the
# character "1" then this will return the integer 123. In addition the
# new index into the string will be returned. For the above example the
# new index would point to the character "3"

proc annotate_depth {string index} {
  set c [string index $string $index]
  set depth 0
  while {$c != "_"} {
    set depth [expr ($depth * 10) + $c]
    incr index
    set c [string index $string $index]
  }
  return [list $depth $index]
}

# proc annotate_retrieve_last_entry_line
#
# Used for textbox widgets. Given a widget pathname return the number of 
# the last line of the textbox which contains some text.

proc annotate_retrieve_last_entry_line {path} {
global TagArray
  if {[regexp $path [array names TagArray]]} {
    return $TagArray($path,endline)
  } else {
    return 1
  }
}

# #####################################################
# REMOVING TagWidgets AND TagArray ENTRIES FOR A WIDGET
# #####################################################

# proc annotate_update_tags
#
# TagWidgets is a list of all widgets that feature tags for
# annotations and natural fonts. This procedure updates TagWidgets by
# removing widget from TagWidgets 

proc annotate_update_tags {widget} {
global TagWidgets
  # Remove all the TagArray entries for the widget.
  annotate_remove_tags $widget
  if {![catch {set TagWidgets}]} {
    set TagWidgetslength [llength $TagWidgets]
    set index 0
    set nuTagWidgets [list]
    # Build a new version of TagWidgets which is the same as the old
    # version but with the given widget name removed. Do this by
    # traversing each widget name in TagWidgets.
    while {$index < $TagWidgetslength} {
      set TagWidgetsentry [lindex $TagWidgets $index]
      if {![string match $widget $TagWidgetsentry]} {
        set nuTagWidgets [concat $nuTagWidgets $TagWidgetsentry]
      }
      incr index
    }
    set TagWidgets $nuTagWidgets 
  }
}

# proc annotate_remove_tags
#
# Given a widget name remove all TagArray entries associated with that
# widget.

proc annotate_remove_tags {widget} {
  catch {annotate_remove_tags_ $widget} error
}

proc annotate_remove_tags_ {widget} {
global TagArray
  set comma ,
  # Since all TagArray indexes use in part the widget name we just
  # traverse a list of all the indices of TagArray and any that match with
  # the widget name we unset.
  set tags [array names TagArray]
  foreach tag $tags {
    if {[regexp $widget$comma $tag]} {
      catch {unset TagArray($tag)}
    }
  }
}

# #################################################
# CONVERSION OF TERMS TO AN INTERNAL REPRESENTATION
# #################################################

# proc annotate_NaturalFont
#
# This takes a term and performs pre-processing to enable the display of 
# proof terms with natural mathematical notation. This includes removing 
# LaTeX markups and replacing them with more easy to use, from a Tcl/Tk
# point of view, markups. Characters of interest are replaced in the
# term to be displayed (which may be a formula or a chunk of text
# containing formulae) with codes of form XBnn where XBnn will be used
# to index into the FontCodes array entry with index nn. For example the 
# substring "\lambda" would be replaced by "XB17". This is so that later 
# processing can detect where to add tags for the display of natural
# fonts. This procedure also removes redundant information such as
# redundant spaces from the term.
#
# A call is then made to annotate_WaveAnnotations to perform a similar
# processing of any wave annotations in the term.

proc annotate_NaturalFont {location term} {
  if {$location != "node"} {
    regsub -all {\)\*} $term \)\n* term
  } else {
    regsub -all {\*\**} $term \* term
  }
  # Remove the slashed brackets (i.e. \\( and \\)'s) that LambdaCLaM
  # puts in to as a result of using LaTeX alltt mode.
  regsub -all {\\\(} $term {} term
  regsub -all {\\\)} $term {} term
  # Remove quotes from extremities of term.
  set term [string trim $term \"]
  # Replace all commas with space.
  regsub -all {\\,} $term { } term
  # Replace all \('s and \)'s with ( or ).
  regsub -all {\\\(} $term \( term
  regsub -all {\\\)} $term \) term
  # Replace all \sb{X} terms with X.
  regsub -all {\\sb\{[0-9][0-9]*\}} $term &SBCLOSE term
  regsub -all {\\sb\{} $term {} term
  regsub -all {\}SBCLOSE} $term {} term
  # Replace all \sp{X} terms with X.
  regsub -all {\\sp\{[a-zA-Z0-9]*\}} $term &SPCLOSE term
  regsub -all {\\sp\{} $term {} term
  regsub -all {\}SPCLOSE} $term {} term
  # Replace the LaTeX math notation codes.
  regsub -all {\\lambda} $term XB17 term
  regsub -all {\\forall2} $term XB00 term
  regsub -all {\\forall} $term XB01 term
  regsub -all {\\exists} $term XB02 term
  regsub -all {\\wedge} $term XB04 term
  regsub -all {\\vee} $term XB18 term
  regsub -all {\\rightarrow} $term XB12 term
  regsub -all {\\vdash} $term XB16 term
  regsub -all {\\in} $term XB08 term
  regsub -all {\\leq} $term XB13 term
  regsub -all {\\geq} $term XB14 term
  regsub -all {\\neg} $term XB11 term
  regsub -all {\\aleph} $term XB03 term
  regsub -all {\\times} $term XB06 term
  # Now remove the dots.
  regsub -all {\ \.\ } $term \. term
  # Now remove extra spaces.
  regsub -all {\ \ *} $term \  term
  regsub -all {\(\ \(} $term \(\(  term
  regsub -all {\)\ \)} $term \)\)  term
  # Now process any wave annotations.
  set term [annotate_WaveAnnotations $term]
  # Remove any extra curly brackets.
  regsub -all \{ $term {} term
  regsub -all \} $term {} term
  return $term
}

# Reminder of character codes for natural mathematical fonts

# \x04e N (nat)
# \x022 forall
# \x024 exists
# \x0d8 not
# \x0ae rightarrow
# \x0de rightarrow two stem
# \x0b9 not equals
# \x0ab <->
# \x0eb <=>
# \x06c lambda
# \x0da vee
# \x0d9 wedge
# \x0a3 leq
# \x0b3 geq
# \x0ce member
# \x0cf not member
# \x0b4 x times

# FontCodes ARRAY
#
# This contains the character codes for mathematical symbols in the 
# Adobe symbol fonts that XBarnacle uses, as well as natural characters
# such as + or ::. The second entry in each list is the character length
# of the symbol. For example to display :: requires two characters.

global FontCodes
set FontCodes(00) [list \x022 1]
set FontCodes(01) [list \x022 1]
set FontCodes(02) [list $ 1]
set FontCodes(03) [list \x04e 1]
set FontCodes(04) [list \x0d9 1]
set FontCodes(05) [list + 1]
set FontCodes(06) [list * 1]
set FontCodes(07) [list 0 1]
set FontCodes(08) [list \x0ce 1]
set FontCodes(09) [list <> 2]
set FontCodes(10) [list :: 2]
set FontCodes(11) [list \x0d8 1]
set FontCodes(12) [list \x0ae 1]
set FontCodes(13) [list \x0a3 1]
set FontCodes(14) [list \x0b3 1]
set FontCodes(15) [list = 1]
set FontCodes(16) [list |- 2] 
set FontCodes(17) [list \x06c 1] 
set FontCodes(18) [list \x0da 1] 

# proc annotate_WaveAnnotations
#
# Given a LaTeX term traverse the term and seek out any wave
# annotations. These will be of form \wf{... or \wfin{ or \wfout or
# \sink{ or \wh{...  
#
# Whenever we enter the scope of an annotation we remove the \wf{ or
# \wh{ or \wfin{ or \wfout or \sink component from the term and replace
# this with a term of form: 
#
#	~XANN_DEPTH_1
#
# Where ANN = of (out front) or if (in front) or wh (hole) or si (sink)
# and DEPTH is the depth of this annotation in any enclosing annotations,
# with annotations with no enclosers having DEPTH 1. So, for example, on 
# encountering a \wfout{ on traversing a term, this would be replaced by
# ~Xof_1_1. If a \wh{ was then encountered this would be replaced by
# ~Xwh_2_1 etc.
#
# Array "brackets" acts as a stack with index variable
# bracket_depth. This is used to keep track of the number of curly
# brackets encountered. If we encounter an opening curly bracket ({) as
# part of a LaTeX annotation markup (e.g. \wfout{) then we increase the
# depth of nesting of brackets so far and store "yes" in brackets to
# indicate that this is an annotation bracket. We also increase a
# variable, ann_depth, which keeps track of the depth of nesting of
# rippling annotations. Else if the bracket is not part of an annotation
# we store "no" in brackets.
#
# If we encounter a close bracket (}) then if the brackets entry for the 
# current depth is "yes" no we just are exiting some LaTeX markup and
# just decrease the depth, bracket_depth. If however the entry is "yes"
# then we are leaving the scope of a LaTeX annotation markup and we add
# a marker to indicate this, this marker having form:
#
#	~1_DEPTH_
#
# where DEPTH is again the depth of nesting of the annotation whose
# scope we are now leaving. We then descrease ann_depth and continue.

proc annotate_WaveAnnotations {term} {
  set tilde "~"
  set length [string length $term]
  # Nuterm holds the processed string.
  set nuterm ""
  # Number of open brackets encountered.
  set bracket_count 0
  # Depth of nesting of annotations so far.
  set ann_depth 0
  # Traverse the term character by character
  for {set i 0} {$i < $length} {incr i} {
    # Get the current character
    set c [string index $term $i]
    # Retrieve the characters from i to i + 3
    set poss_ann [string range $term $i end]
    set increase_due_to_ann -1
    set end "_1 "
    # Are the next characters forming a LaTeX annotation
    # markup - if so then the ann_depth variable holding the depth of
    # nesting of annotations is incremented, the appropriate marker
    # (~XANN_DEPTH_1) indicating that the scope of an annotation has
    # been entered is formed, and an increase_due_to_ann variable is set 
    # indicating how many characters must be skipped before traversal of
    # the term continues - this is so that the rest of the LaTeX
    # annotation markup for the currently encountered annotation can be
    # ignored 
    # Outward wave-front (default for \wf)
    if {[regexp {^\\wf\{} $poss_ann]} {
      incr ann_depth
      set ann " ~Xof_$ann_depth$end"
      set increase_due_to_ann 3
    # Outward wave-front
    } elseif {[regexp {^\\wfout\{} $poss_ann]} {
      incr ann_depth
      set ann " ~Xof_$ann_depth$end"
      set increase_due_to_ann 6
    # Inward wave-front
    } elseif {[regexp {^\\wfin\{} $poss_ann]} {
      incr ann_depth
      set ann " ~Xif_$ann_depth$end"
      set increase_due_to_ann 5
    # Wave-hole
    } elseif {[regexp {^\\wh\{} $poss_ann]} {
      incr ann_depth
      set ann " ~Xwh_$ann_depth$end"
      set increase_due_to_ann 3
    # Sink
    } elseif {[regexp {^\\sink\{} $poss_ann]} {
      incr ann_depth
      set ann " ~Xsi_$ann_depth$end"
      set increase_due_to_ann 5
    }
    # If an annotation was encountered...
    if {$increase_due_to_ann != -1} {
      # Add the XBarnacle annotation markup to the processed term
      set nuterm $nuterm$ann
      # Increase the count of curly brackets encountered
      incr bracket_count
      # Mark that traversal is directly within the scope of an
      # annotation 
      set brackets($bracket_count) yes
      # Update the index into the term
      set i [expr $i + $increase_due_to_ann]
      set increase_due_to_ann -1
    # Else if a standard curly open bracket was encountered...
    } elseif {$c == "\{"} {
      # Standard open curly bracket
      # Increase the count of curly brackets encountered
      incr bracket_count
      # Mark that traversal is directly within the scope of an
      # annotation 
      set brackets($bracket_count) no
      set lb "\{"
      # Put the curly bracket into the processed term
      set nuterm $nuterm$lb
    # Else if a standard curly close bracket was encountered...
    } elseif {$c == "\}"} {
      if {$brackets($bracket_count) == "yes"} {
        # Then traversal is leaving the scope of an annotation markup
        # Form the exiting scope of annotation markup (~1_DEPTH_)
        set under "_"
        set marker "~1_$ann_depth$under~"
        # Decrease by 1 the counts of the nesting of brackets and
        # nesting of annotation 
        set bracket_count [expr $bracket_count - 1]
        set ann_depth [expr $ann_depth - 1]
        # Add markup to term
        set nuterm $nuterm\ $marker\ 
      } else {
        # Standard closing curly bracket
        set rb "\}"
        # Add curly bracket to processed term
        set nuterm $nuterm$rb
        # Decrease by 1 the counts of the nesting of brackets
        set bracket_count [expr $bracket_count - 1]
      }
    } else {
      # Just add the character to the processed term
      set nuterm $nuterm$c
    }
  }
  return $nuterm
}

# ######################################
# TOGGLING ON/OFF DISPLAY OF ANNOTATIONS
# ######################################

# proc annotate_show_annotations
#
# Update the display of annotations in light of either changes to the
# colours used to display one or more annotations or whether the user
# has toggled the annotation on or off using the Ripple menu.

proc annotate_show_annotations {} {
global TagWidgets TagArray colours TogColour xb
  # For each annotation check if it is enabled for display or not. If so
  # then set entries of a TogColour array to be those for the annotation
  # as retrieved from the colours array. Else just set the entries for
  # the annotation to be the default foreground and background colours.
  foreach ann $xb(annotations) {
    if {$xb(annotations,$ann,on)} {
      set TogColour($ann,fore) $colours($ann,fore)
      set TogColour($ann,back) $colours($ann,back)
    } else {
      set TogColour($ann,fore) $colours(default,fore)
      set TogColour($ann,back) $colours(default,back)
    }
  }
  # If there are widgets with annotations then...
  if [info exists TagArray] {
    # For each widget that has tags for annotations
    foreach widget $TagWidgets {
      # Process each tag associated with the widget
      for {set tag 0} {$tag <= $TagArray($widget,tagnumber)} {incr tag} {
        annotate_shading_update $widget $tag
      }
      # If the widget is a canvas then...
      if {$TagArray($widget,type) == "canvas"} {
	# Process each tag associated with letters in the widget
        set lenf [string length $TagArray($widget,term)]
        for {set letters 0} {$letters <= $lenf} {incr letters} {
	  annotate_letters_update $widget $letters
        }
      }
    }
  }
}

# proc annotate_text_canvas
#
# Update the colours of an annotation in widget and with index
# index. Fore and back hold the new colours for the foreground and
# background. 

proc annotate_text_canvas {widget index fore back} {
global TagArray
  if {$TagArray($widget,type) == "text" } {
    # For textboxes just update the foreground and background colours
    $widget tag configure $index -foreground $fore -background $back
  } else {
    # For canvases just set the background colour of the tagged widget
    $widget itemconfigure rect$index -outline $back
    $widget itemconfigure rect$index -fill $back
  }						
}

# proc annotate_letters_update
#
# Update the colour of letters on a canvas widget. Use TagArray to
# retrieve the type of annotation that this tag represents and then
# TogColour to retrieve the colour to be used.

proc annotate_letters_update {widget letters} {
global TagArray TogColour
  # Find the type of annotation in which this letter occurs (e.g. is it
  # a wave front, hole, sink or nothing)
  set encloser [annotate_FindEnclosingAnnotation $widget $letters]
  if {$encloser != -1} {
    # If letter is within a widget that is used for annotation shading
    # then update the colour of the letter
    $widget itemconfigure lett$letters -fill \
      $TogColour($TagArray($widget,$encloser,type),fore)
  }
}

# proc annotate_shading_update
#
# Given a tag in a widget call annotate_text_canvas to update the colour 
# of the widget associated with this tag. Use TagArray to retrieve the
# type of annotation that this tag represents and then TogColour to
# retrieve the colour to be used.

proc annotate_shading_update {widget tag} {
global TagArray TogColour
  annotate_text_canvas $widget $tag \
    $TogColour($TagArray($widget,$tag,type),fore) \
    $TogColour($TagArray($widget,$tag,type),back)
}

# proc annotate_update_ripple_keys
#
# If the user changes the colours used to display rippling annotations
# then update the colour key on the display to reflect this.

proc annotate_update_ripple_keys {} {
global xb colours 
  foreach ann $xb(annotations) {
    [gui_retrieve_window ripple_key].$ann configure -fg \
      $colours($ann,fore) -bg $colours($ann,back)
    }
}

# proc annotate_reset_buttons
#
# Set the state of XBarnacle so that all annotations will be displayed
# Then call annotate_show_annotations to display the annotations.

proc annotate_reset_buttons {} {
global xb
  foreach ann $xb(annotations) {
    set xb(annotations,$ann,on) 1
  }
   annotate_show_annotations
}
