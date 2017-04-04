# ###########################
# ###########################
#
# CHANGING ANNOTATION COLOURS
#
# ###########################
# ###########################

# proc colours_load_xb_colours
#
# Load in existing colour scheme for wave annotations (stored in an
# XB_colours file) or else reset to a default scheme if there is no
# existing colour scheme.

proc colours_load_xb_colours {} {
global env colours
  if [catch {source $env(HOME)/.XB_colours} result] {
    colours_save_xb_colours
  }
}

# proc colours_save_xb_colours
#
# Save the wave annotation colours in an XB_colours file.

proc colours_save_xb_colours {} {
global colours env
  # Retrieve list of indexes into array colours
  set typnames [array names colours]
  if [file exists $env(HOME)/.XB_colours] {
    exec rm -f $env(HOME)/.XB_colours
  }
  set file [open $env(HOME)/.XB_colours a+]
  # Write out the colours array
  foreach val $typnames {
    puts $file "set colours($val) $colours($val)"
  }
  close $file
}

# proc colours_change_colour
#
# When the user selects a new colour for an annotation the radio
# button corresponding to that annotation is updated to reflect the
# new colour scheme. The new colour for that annotation is also saved
# in the colours array.

proc colours_change_colour {W y} {
global colours Colour_location Colour_annotation
  $W select set [$W nearest $y]
  set colour [lindex [selection get] 0]
  # The annnotation whose colour has been changed
  set type [lindex $Colour_annotation 0]
  # The pathname of the radio button corresponding to this colour
  set radio [lindex $Colour_annotation 1]
  # Colour_location indicates whether the foreground or background
  # colour for the annotation has been changed - taking values fore
  # or back
  set colours($type,$Colour_location) $colour
  # Update the radio buttons
  set ground ground
  $radio config -$Colour_location$ground \
    $colours($type,$Colour_location)
}

# proc colours_colour_chooser
#
# Draw an interface to allow the user to select the colours for the wave 
# annotations (both foreground, ink, colours and background, paper,
# colours).

proc colours_colour_chooser {} {
global colours xb Colours
  destroy .colourTOP
  set choosewin [toplevel .colourTOP]
  wm title $choosewin "XBarnacle - Rippling Colour Chooser"
  wm geometry $choosewin +300+300
  $choosewin config -bg $xb(bg)
  label $choosewin.title -bg $xb(bg) -fg $xb(fg) -bd 2 -font $xb(font) \
    -text "Select entity for colour change:"
  pack $choosewin.title -side top -fill x
  frame $choosewin.radio -bg $xb(bg)
  pack $choosewin.radio -side top 
  # Add a radiobutton for each type of wave annotation, coloured using
  # the existing colour settings for that annotation
  foreach type $xb(annotations) {
    set name $xb(annotations,$type)
    set value [list $type $choosewin.radio.$type]
    radiobutton $choosewin.radio.$type -font $xb(font) -relief raised \
      -fg $colours($type,fore) -bg $colours($type,back) \
      -activeforeground $colours($type,fore) \
      -activebackground $colours($type,back) -text $name -variable \
      Colour_annotation -value $value
    pack $choosewin.radio.$type -side left -fill x -expand true
    $choosewin.radio.$type invoke
  }
  label $choosewin.title2 -bg $xb(bg) -fg $xb(fg) -font $xb(font) \
    -text "Select whether to change ink or paper:"
  pack $choosewin.title2 -side top -fill x
  frame $choosewin.groundsel
  pack $choosewin.groundsel -side top
  # Paper/Background radiobutton
  radiobutton $choosewin.groundsel.back -font $xb(font) -relief raised \
    -text "Paper" -variable Colour_location -value back -bg $xb(bg) \
    -fg $xb(fg) -activebackground $xb(abg) -activeforeground $xb(afg)
  # Ink/foreground radiobutton
  radiobutton $choosewin.groundsel.fore -font $xb(font) -relief raised \
    -text "Ink" -variable Colour_location -value fore -bg $xb(bg) -fg \
    $xb(fg) -activebackground $xb(abg) -activeforeground $xb(afg)
  pack $choosewin.groundsel.fore -side left -fill x -expand true
  pack $choosewin.groundsel.back -side left -fill x -expand true
  # Default select Ink radiobutton
  $choosewin.groundsel.fore invoke
  label $choosewin.title3 -bg $xb(bg) -fg $xb(fg) -font $xb(font) \
    -text "Select new colour:"
  pack $choosewin.title3 -side top -fill x
  frame $choosewin.colour -bg $xb(bg) -relief sunken -bd 0
  pack $choosewin.colour -fill both -side top -expand true
  set path $choosewin.colour
  listbox $path.listbox -bg white -fg $xb(fg) -bd 2 -selectbackground \
    $xb(fg) -selectforeground white -relief sunken -cursor $xb(cursor) \
    -font $xb(font) -setgrid 1 -yscroll "$path.ysc set" 
  pack $path.listbox -side left -fill both -expand true
  scrollbar $path.ysc -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$path.listbox yview" -orient \
    vertical -bd 1 -relief sunken -cursor $xb(cursor)
  pack $path.ysc -side left -fill y
  bind $path.listbox <Double-1> "colours_change_colour %W %y"
  # Insert available colours into the listbox
  foreach colour $Colours {
    $path.listbox insert end $colour
  }
  set doneframe [frame $choosewin.quit]
  button $doneframe.done -text "OK" -font $xb(font) -fg $xb(fg) -bg \
    $xb(bg) -command "colours_accept .colourTOP"
  button $doneframe.cancel -text "Cancel" -font $xb(font) -fg $xb(fg) \
    -bg $xb(bg) -command "colours_reject .colourTOP" 
  pack $doneframe.done $doneframe.cancel -side left
  pack $doneframe -side bottom
  wm protocol .colourTOP WM_DELETE_WINDOW {set z 0}
}

# proc colours_reject
# proc colours_accept
#
# Actions to take when exiting the colour choosing activity.

proc colours_reject {path} {
 # Load previously saved colours
 colours_load_xb_colours
 destroy $path
}

proc colours_accept {path} {
  destroy $path
  # Save new colours
  colours_save_xb_colours
  # Update the annotation tags to reflect the new colours
  annotate_show_annotations
  # Update the ripple key to reflect the new colours
  annotate_update_ripple_keys
} 
