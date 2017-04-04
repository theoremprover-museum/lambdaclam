# #######
# #######
#
# TRACING
#
# #######
# #######

# #################
# SET TRACING LEVEL
# #################

# proc trace_select_trace
#
# Retrieve a new trace level from the user and then send a request to
# LambdaCLaM for it to make this the new trace level.

proc trace_select_trace {} {
global xb Old_level
  set Old_level [var_retrieve_trace_level]
  set path .select_trace
  destroy $path
  toplevel $path
  wm title $path "Trace"
  $path configure -bg $xb(bg)
  label $path.label -fg $xb(fg) -bg $xb(bg) -font $xb(font) -text \
    "Enter trace level:" 
  pack $path.label -side top -fill x
  entry $path.level -fg $xb(fg) -bg $xb(bg) -font $xb(font) \
    -textvariable Old_level
  pack $path.level -side top -fill x
  frame $path.butts -bg $xb(bg)
  pack $path.butts -side bottom
  button $path.butts.ok -text "OK" -bg $xb(bg) -fg $xb(fg) -font \
    $xb(font) -command {destroy .select_trace; \
    trace_update_trace_level $Old_level}
  pack $path.butts.ok -side left
  bind $path.level <Return> {destroy .select_trace; \
    trace_update_trace_level $Old_level}
  button $path.butts.close -text "Close" -bg $xb(bg) -fg $xb(fg) \
    -font $xb(font) -command "destroy $path"
  pack $path.butts.close -side left
  focus $path.level
}

# proc trace_update_trace_level
#
# Update the trace level then initiate a LambdaCLaM action to ensure
# that LambdaCLaM updates its trace level.

proc trace_update_trace_level {level} {
  var_set_trace_level $level
  misc_lambda_clam_action set_trace
}

# ##############################
# DISPLAYING TRACING INFORMATION
# ##############################

# proc trace_add_trace_information
#
# Args contains tracing information to be displayed in the tracing
# window. Note that args is a general Tcl/Tk identifier for when the
# number of arguments a procedure may have is not known - here it is
# being used to handle cases where trace information may have spaces or
# line-breaks in it. Args can be treated like any list.
#
# A call to annotate_retrieve_last_entry_line is used so that the last
# line in which text was placed in the trace window textbox can be
# retrieved. This is used as part of the call to annotate_text_widget to
# place the new trace information into the trace window textbox after
# any existing information and means that it is only neccessary to
# calculate tag information for annotations and natural fonts for the
# newly added trace information rather than the entire contents of the
# textbox.

proc trace_add_trace_information {args} {
  # If the trace window is present...
  if {[winfo exists [gui_retrieve_window trace]]} {
    set text "\n$args"
    set endline [annotate_retrieve_last_entry_line \
      [gui_retrieve_window trace_text]]
    # Insert the text into the trace window, suitably processed to
    # handle natural fonts and wave annotations
    annotate_text_widget text [gui_retrieve_window \
      trace_text] $text $endline
  }
}

# proc trace_clear_trace_window
#
# Delete the text in the trace textbox then update the tag information
# to denote that this widget does not at present have any annotations or 
# natural fonts in it.

proc trace_clear_trace_window {} {
  catch {[gui_retrieve_window trace_text] delete 0.0 end}
  annotate_update_tags [gui_retrieve_window trace_text]
}

# proc trace_create_trace_window
#
# Place a window on screen to be used for displaying tracing
# information.

proc trace_create_trace_window {} {
global xb
  set TraceTop .trace
  destroy $TraceTop
  toplevel $TraceTop
  wm title $TraceTop "Trace Information"
  wm geometry $TraceTop +450+450
  $TraceTop configure -bg $xb(bg)
  frame $TraceTop.butt -bg $xb(bg) 
  pack $TraceTop.butt -side bottom
  button $TraceTop.butt.clear -fg $xb(fg) -bg $xb(bg) -cursor \
    $xb(cursor) -font $xb(font) -relief raised -bd 3 -activebackground \
    $xb(abg) -activeforeground $xb(afg) -text "Clear" -command \
    "trace_clear_trace_window"
  pack $TraceTop.butt.clear -side left
  button $TraceTop.butt.cancel -fg $xb(fg) -bg $xb(bg) \
    -cursor $xb(cursor) -font $xb(font) -relief raised -bd 3 \
    -activebackground  $xb(abg) -activeforeground $xb(afg) -text \
    "Close" -command "destroy $TraceTop"
  pack $TraceTop.butt.cancel -side left 
  scrollbar $TraceTop.yscroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$TraceTop.text yview" -orient \
    vertical -bd 1 -relief sunken -cursor $xb(cursor)
  pack $TraceTop.yscroll -side right -fill y
  scrollbar $TraceTop.xscroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$TraceTop.text xview" -orient \
    horizontal -bd 1 -relief sunken -cursor $xb(cursor)
  pack $TraceTop.xscroll -side bottom -fill x
  text $TraceTop.text -fg black -background white -cursor $xb(cursor) \
    -relief flat -xscrollcommand "$TraceTop.xscroll set" \
    -yscrollcommand "$TraceTop.yscroll set" -font $xb(font) -wrap word
  bind $TraceTop.text <Destroy> "trace_destroy_trace_window"
  $TraceTop.text tag configure symbolo -font $xb(fontmaths14)
  pack $TraceTop.text -side left -fill both -expand true
  return [list $TraceTop $TraceTop.text]
}

# proc trace_destroy_trace_window
#
# Call trace_clear_trace_window to update the system so that records of
# the tags for natural fonts and annotations for the trace window are
# wiped. Then set xb(trace_window) to 0.

proc trace_destroy_trace_window {} {
global xb
  trace_clear_trace_window
  set xb(trace_window) 0
}

# proc trace_clear_view_trace_window
#
# Used to toggle display/removal of the trace window via the Viewing
# Trace Window option in the Options menu.

proc trace_clear_view_trace_window {} {
global xb
  if {!$xb(trace_window)} {
    destroy [gui_retrieve_window trace]
  } else {
    trace_create_trace_window
  }
}
