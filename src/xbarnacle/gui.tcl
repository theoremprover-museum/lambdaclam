# ################################
# ################################
#
# XBARNACLE INTERFACE PRESENTATION
#
# ################################
# ################################

# ############
# gui DATATYPE
# ############

# Since we often need to access the pathnames of widgets the gui array
# stores common pathnames. This avoids the requirement for hard coding
# pathnames into code when we need to, for example, disable a certain
# button.
#
# At present the entries of this array will include:
#
# gui(toplevel) - pathname of main XBarnacle window
# gui(pda) - pathname of canvas widget that displays the proof tree
# gui(zoom_in) - pathname of zoom in button
# gui(zoom_out) - pathname of zoom out button
# gui(play) - pathname of play button
# gui(step) - pathname of step button
# gui(stop) - pathname of stop button
# gui(pause) - pathname of pause button
# gui(abandon) - pathname of abandon button
# gui(trace) - pathname of trace window
# gui(trace_text) - pathname of textbox in trace window that displays
#                 - trace information
# gui(menu_<name>) - pathnames of menus in the menubar (one entry for
#                  - each menu
#
# The following two procedures allow the setting of gui entries and,
# given an index name, (for example zoom_in or pda) the retrieval of the 
# pathname.

proc gui_retrieve_window {type} {
global gui
  return $gui($type)
}

proc gui_set_window {path type} {
global gui
  set gui($type) $path
}

# #############################
# CREATE MAIN XBARNACLE BUTTONS
# #############################

# proc gui_XB_button
#
# Draw a button on screen using the given information as to its
# pathname, command, bitmap, position and bind some balloon help to
# it.

proc gui_XB_button {path command bitmap position help} {
global xb 
  button $path -fg $xb(fg) -bg $xb(bg) -cursor $xb(cursor) -font \
    $xb(font) -relief raised -bd 3 -activebackground $xb(abg) \
    -activeforeground $xb(afg) -command $command -bitmap $bitmap
  pack $path -side $position
  help_set_balloon $path $help
  return $path
}

# proc gui_createNavigButtons
#
# Create buttons for navigating through proof tree.

proc gui_createNavigButtons {navigFrame} {
global xb
  label $navigFrame.title -text "Navigation" -font $xb(font) -bg \
    $xb(bg) -fg $xb(fg) 
  pack $navigFrame.title -side top -fill x
  # Goto Root button
  button $navigFrame.root -fg $xb(fg) -bg $xb(bg) -font $xb(font) \
    -pady 1 -text "Goto Root" -command navig_goto_root
  pack $navigFrame.root -side left
  help_set_balloon $navigFrame.root "Move the display so\nthe root node \
    is visible on screen"
  # Goto Current button
  button $navigFrame.curr -fg $xb(fg) -bg $xb(bg) -font $xb(font) \
    -pady 1 -text "Goto Current" -command navig_goto_current
  pack $navigFrame.curr -side left
  help_set_balloon $navigFrame.curr "Move the display so\nthe current node \
    is visible on screen"
  # Goto Node... button
  button $navigFrame.any -fg $xb(fg) -bg $xb(bg) -font $xb(font) \
    -pady 1 -text "Goto Node..." -command navig_goto_user_given
  pack $navigFrame.any -side left
  help_set_balloon $navigFrame.any "Allows selection of a\nnode to be \
    centered on screen"
}

# proc gui_createZoomButtons
#
# Create buttons for zooming proof.

proc gui_createZoomButtons {zoomFrame} {
global xb env
  label $zoomFrame.title -text "Zoom" -bg $xb(bg) -fg $xb(fg) \
    -font $xb(font) 
  pack $zoomFrame.title -side top -fill x
  # Zoom In button
  gui_set_window [gui_XB_button $zoomFrame.zoomin navig_zoom_in_cmds \
    @$env(LCLAM_GUI_DIR)/bitmaps/zoomout.bitmap right "Display the \
    proof tree in less detail"] zoom_in
  # Zoom Out button
  gui_set_window [gui_XB_button $zoomFrame.zoomout navig_zoom_out_cmds \
    @$env(LCLAM_GUI_DIR)/bitmaps/zoomin.bitmap right "Display the \
    proof tree in more detail"] zoom_out
  [gui_retrieve_window zoom_out] configure -state disabled
}

# proc gui_createPlanButtons
#
# Create buttons for planning.

proc gui_createPlanButtons {planFrame} {
global xb env
  label $planFrame.title -text "Proof" -bg $xb(bg) -fg $xb(fg) -font \
    $xb(font)
  pack $planFrame.title -side top -fill x
  # Abandon button
  gui_set_window [gui_XB_button $planFrame.stop plan_stop_commands \
    @$env(LCLAM_GUI_DIR)/bitmaps/stop.bitmap right "Abandon \
    current proof"] stop
   # Pause button
  gui_set_window [gui_XB_button $planFrame.pause plan_pause_commands \
    @$env(LCLAM_GUI_DIR)/bitmaps/pause.bitmap right \
    "Stop CLaM performing proof steps"] pause
  # Backtrack button
  gui_set_window [gui_XB_button $planFrame.back plan_back_commands \
    @$env(LCLAM_GUI_DIR)/bitmaps/back.bitmap right \
    "Cause CLaM to backtrack"] back
  # Proof Step button
  gui_set_window [gui_XB_button $planFrame.step plan_step_commands \
    @$env(LCLAM_GUI_DIR)/bitmaps/step.bitmap right \
    "Cause CLaM to perform\na single proof step"] step
  # Multiple Proof Steps button
  gui_set_window [gui_XB_button $planFrame.play plan_play_commands \
    @$env(LCLAM_GUI_DIR)/bitmaps/play.bitmap right \
    "Cause CLaM to perform\nproof steps until stopped"] play
}

# proc gui_create_interface_buttons
#
# Create the main interface buttons.

proc gui_create_interface_buttons {Frame} {
global xb
  set buttonFrame $Frame.buttonbar
  frame $buttonFrame -bg $xb(bg) -bd 1 -cursor $xb(cursor)
  pack $buttonFrame -side top -fill x
  # Navigation buttons frame
  set navigFrame $buttonFrame.navigFrame
  frame $navigFrame -bg $xb(bg)
  pack $navigFrame -side left -anchor center
  gui_createNavigButtons $navigFrame
  # Zoom buttons frame
  set zoomFrame $buttonFrame.zoomFrame
  frame $zoomFrame -bg $xb(bg) -bd 1 -cursor $xb(cursor)
  pack $zoomFrame -side left
  gui_createZoomButtons $zoomFrame
  # Planning buttons frame
  set planFrame $buttonFrame.planFrame
  frame $planFrame -bg $xb(bg) -bd 1 -cursor $xb(cursor)
  pack $planFrame -side right
  gui_createPlanButtons $planFrame
}

# ##################################
# CREATE PROOF DISPLAY AREA AND KEYS
# ##################################

# proc gui_create_proof_display_area
#
# Create a canvas for displaying a proof tree.

proc gui_create_proof_display_area {window} {
global xb
  set pdaFrame $window.pdaFrame
  frame $pdaFrame -bg white -bd 1 -cursor $xb(cursor)
  pack $pdaFrame -side top -fill both -expand true -anchor nw
  scrollbar $pdaFrame.yScroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$pdaFrame.pdaCanvas yview" \
    -orient vertical -bd 1 -relief sunken -cursor $xb(cursor)
  pack $pdaFrame.yScroll -side right -fill y
  scrollbar $pdaFrame.xScroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$pdaFrame.pdaCanvas xview" -orient \
    horizontal -bd 1 -relief sunken -cursor $xb(cursor)
  pack $pdaFrame.xScroll -side bottom -fill x
  gui_create_colour_code_keys $pdaFrame
  canvas $pdaFrame.pdaCanvas -background white -bd 1 -closeenough 0 \
    -cursor $xb(cursor) -confine false -relief flat \
    -scrollregion {-50c 0c 50c 50c} -xscrollcommand \
    "$pdaFrame.xScroll set" -yscrollcommand "$pdaFrame.yScroll set" \
    -highlightthickness 0 
  pack $pdaFrame.pdaCanvas -side left -fill both -expand true
  gui_set_window $pdaFrame.pdaCanvas pda
}

# proc gui_create_colour_code_keys
#
# In the given window create some labels showing the key for node status 
# and rippling colours.

proc gui_create_colour_code_keys {window} {
global xb node colours
  set buttFrame $window.buttFrame
  frame $buttFrame -bg white -bd 1 -cursor $xb(cursor)
  pack $buttFrame -side top -fill x
  set statFrame $buttFrame.statFrame
  frame $statFrame -bg white -bd 1 -cursor $xb(cursor)
  pack $statFrame -side left -fill x -expand true
  label $statFrame.label -text "Node Key:" -fg black -bg white \
    -font $xb(font)
  pack $statFrame.label -side left -padx 2 -expand true -fill x
  # Add an entry for each state a node can take
  foreach state $node(states) {
    label $statFrame.$state -text $node($state,prez) -fg black \
      -bg $node($state,colour) -bd 1 -font $xb(font)
    pack $statFrame.$state -side left -padx 2 -expand true  -fill x
  }
  set rippFrame $buttFrame.rippFrame
  frame $rippFrame -bg white -bd 1 -cursor $xb(cursor)
  pack $rippFrame -side left -fill x -expand true
  label $rippFrame.label -text "Ripple Key:" -fg black -bg white -font \
    $xb(font)
  pack $rippFrame.label -side left -padx 2 -expand true -fill x
  # Add an entry for each type of rippling annotation
  foreach ann [lsort $xb(annotations)] {
    label $rippFrame.$ann -text $xb(annotations,$ann) \
      -fg $colours($ann,fore) -bg $colours($ann,back) -bd 1 -font \
      $xb(font) 
    pack $rippFrame.$ann -side left -padx 2 -expand true -fill x 
  }
  gui_set_window $rippFrame ripple_key
}

# ######################
# CREATE XBARNACLE MENUS
# ######################

# proc gui_setup_menu
#
# Create a menu from the given information - xlabel is the pathname for
# a menu widget and xlist holds information about the contents of the
# menu, that is, the widgets (buttons, checkbuttons, separators etc)
# that are to be placed into the window. Each element of xlist is a
# list. These elements will be one of the following:
#
# For menu separator lines:
#   {separator}
# For standard menu commands:
#   {command <command_label> <command_procedure>}
# For radio buttons:
#   {radio <radio_label> <radio_command_procedure> <radio_variable>}
# For checkboxes:
#   {check <check_label> <check_command_procedure> <check_variable>}

proc gui_setup_menu {xlist xlabel} {
global xb
  foreach i $xlist {
    switch -- [lindex $i 0] {
      separator {
        $xlabel add separator
      }
      command {
        $xlabel add command -label [lindex $i 1] \
          -command [lindex $i 2]
      }
      radio {
        $xlabel add radio -label [lindex $i 1] \
          -command [lindex $i 2] -variable [lindex $i 3]
      }
      check {
        $xlabel add check -label [lindex $i 1] \
          -command [lindex $i 2] -variable [lindex $i 3]
      }
      default {
      }
    }
  }
}

# proc gui_create_xbarnacle_menubar
#
# Creates the XBarnacle menubar - sets up the information about the
# menus and sub-menus - see gui_setup_menu and gui_create_menus comments
# for the format of the information that is formed in this procedure.

proc gui_create_xbarnacle_menubar {window} {
global gui
  set file \
    {{command {Load Theory File...} misc_load_library_file} \
     {command {Edit Theory File...} misc_edit_library_file} \
     {separator} \
     {command {Quit} misc_quit_commands}}
  set view {{command {Queries...} misc_view_queries}}
  set plan {{command {Select Query to Plan...} misc_plan_queries}}
  set sym_eval \
     {
      {command {Enable/Disable Rewrite...}  misc_enable_disable_rewrites}
    # Gordon 30/5/00
      {command {Choose Wave Rules...}  misc_choose_wave_rules}
     }
  # gui_ripple_menu procedure is called to form the information for the
  # Ripple menu
  set ripple [linsert [gui_ripple_menu] end {separator}]
  set ripple [linsert $ripple end {command {Rippling display \
    colours...} colours_colour_chooser}]
  set options \
    {{check {Node Addresses on Tree} \
      destroy_then_display_tree node(addresses)} \
    {check {Display Follows Current Node} {} xb(displayfollow)} \
    {check {Viewing Trace Window} trace_clear_view_trace_window \
      xb(trace_window)} \
    {separator} \
    {command {Set Tracing Level...} trace_select_trace}}
  # Gordon 12/3/00
  set methods \
    { {command {List Methods} misc_list_methods} \
      {command {Set Top Method} misc_set_top_meth}}
  set help \
    {{command {Proof Trees} help_proof_tree_help} \
     {command {Node Addresses} help_node_address_help}\
     {command {Lclam Interactive} misc_lclam_interactive }}
  set menu_labels "\
    {File {$file} \
      {Commands for loading and deleting\nCLaM objects and proofs} 
      left} \
    {View {$view} \
      {Commands for viewing loaded CLaM objects} left} \
    {Plan {$plan} \
      {Commands for selecting a theorem to prove} left} \
    {Rewrites {$sym_eval} {Rewrite rule commands} left} \
    {Ripple {$ripple} \
      {Commands for toggling wave shading and\nselecting \
      rippling display colours} left} \
    {Options {$options} \
      {Toggling various XBarnacle display\nand operational features} \
      left} \
    {Methods {$methods} {Method selection commands} left} \
    {Help {$help} {Online help instructions} right}"
  gui_create_menus $window.menubar $menu_labels
}

# proc gui_create_menus
#
# Given a menubar widget pathname add menus to the menubar - the menu
# contents, commands and headings are all stored in menu_labels. 
# menu_labels is a list of elements each with the following structure:
#
# {<Menu Label> <List Of Information of Contents of Menu (as described
# in comments for gui_setup_menu)> <Balloon help comment> <Location where
# menu label is to be packed in menu bar (left or right)> }.

proc gui_create_menus {path menu_labels} {
global xb
  frame $path -bg $xb(bg) -bd 2 -relief raised -cursor $xb(cursor)
  pack $path -side top -fill x
  foreach item $menu_labels {
    set name [lindex $item 0]
    gui_set_window [menubutton $path.a$name -text $name -menu \
      $path.a$name.menu -bg $xb(bg) -fg $xb(fg) -activebackground \
      $xb(abg) -activeforeground $xb(afg) -bd 2 -cursor $xb(cursor) \
      -font $xb(font) -padx 4 -pady 2] menu_$name
    set side [lindex $item 3] 
    pack $path.a$name -side $side -padx 1 -pady 2
    menu $path.a$name.menu -bg $xb(bg) -fg $xb(fg) -bd 2 \
      -activebackground $xb(abg) -activeforeground $xb(afg) \
      -cursor $xb(cursor) -font $xb(font)
    gui_setup_menu [lindex $item 1] $path.a$name.menu
    help_set_balloon $path.a$name [lindex $item 2]
  }
}

# proc gui_ripple_menu
#
# Retrieve information about the current status of rippling annotations
# i.e. is XBarnacle toggled to display each annotation or not. Used in
# the display of the Ripple menu to correctly set the checkboxes. The
# format of the elements of the list ripple is as described in the
# comments for gui_setup_menu.

proc gui_ripple_menu {} {
global xb
  set ripple {}
  foreach ann [lsort $xb(annotations)] {
    set tmp "check {$xb(annotations,$ann)} annotate_show_annotations \
      [concat xb(annotations,$ann,on)]"
    lappend ripple $tmp
  }
  return $ripple
}

################################
# DRAW THE MAIN XBARNACLE WINDOW
################################

# Initialise XBarnacle

proc gui_xbarnacle_initialise {} {
global xb env
  set toplevel [gui_set_window .xBarnacle toplevel]
  toplevel $toplevel
  wm title $toplevel "X-Barnacle"
  wm minsize $toplevel 400 100
  $toplevel configure -background $xb(bg) -borderwidth 2 -height \
    200 -relief sunken -width 100 -cursor $xb(cursor)
  wm geometry $toplevel +100+100
  wm iconbitmap $toplevel @$env(LCLAM_GUI_DIR)/bitmaps/x-barnacle.bitmap 
  # Load any preferred colour scheme
  colours_load_xb_colours
  # Add the interface widgets
  gui_create_xbarnacle_menubar $toplevel
  gui_create_interface_buttons $toplevel
  gui_create_proof_display_area $toplevel
  # Draw the trace window
  # Tried to make trace window non-starter : Gordon - needs fixed
  set trace [trace_create_trace_window]
  gui_set_window [lindex $trace 0] trace
  gui_set_window [lindex $trace 1] trace_text
  # Initialise XBarnacle
  plan_new_query ""
  plan_set_buttons_not_planning
  annotate_reset_buttons
  annotate_show_annotations
  tkwait visibility $toplevel
}
