# ##############################################
# ##############################################
#
# TREE NAVIGATION, BROWSING AND SCALING COMMANDS
#
# ##############################################
# ##############################################

# #####################################
# RESIZING SELECTED NODES AND SUB-TREES
# #####################################

proc navig_resize_branch_option {node_id} {
  navig_resize_option_general $node_id 1
}

proc navig_resize_option {node_id} {
  navig_resize_option_general $node_id 0
}

# proc navig_resize_option_general {<node_address>,<branch_flag>}
#
# If branch_flag is not set then change the size of the displayed node
# with address, node_address. This toggles from goal view to method view
# to box view to goal view...
# If branch_flag is set then change the size of the displayed node with
# address, node_address, and similarly set all the nodes in the sub-tree 
# rooted at this node to be the same size as the selected node. Again
# this toggles from goal view to method view to box view to goal view...

proc navig_resize_option_general {node_id branch} {
  switch -- [var_return_node_value $node_id type] {
    box {
      set type goal
    }
    method {
      set type box
    }
    goal {
      set type method
    }
  }
  # Update the current setting for how this node is viewed.
  var_set_node_value $node_id type $type
  if {$branch} {
    # Update the current setting for how this nodes descendants are viewed.
    foreach n [tree_get_descendants $node_id] {
      var_set_node_value $n type $type
    }
  }
  # Redraw the tree
  tree_refresh
}

# #############
# ZOOM COMMANDS
# #############

# proc navig_zoom_out_cmds
#
# Change the size of every node on the display. If the setting for the
# proof tree is box view then zoom to method view, if method view then
# zoom to goal view.

proc navig_zoom_out_cmds {} {
  if {[var_retrieve_node_type] == "box"} {
    navig_zoom_toggle_cmds normal normal method
  } else {
    navig_zoom_toggle_cmds normal disabled goal
  }
}

# proc navig_zoom_in_cmds
#
# Change the size of every node on the display. If the setting for the
# proof tree is goal view then zoom to method view, if method view then
# zoom to box view.

proc navig_zoom_in_cmds {} {
  if {[var_retrieve_node_type] == "goal"} {
    navig_zoom_toggle_cmds normal normal method
  } else {
    navig_zoom_toggle_cmds disabled normal box
  }
}

# proc navig_zoom_toggle_commands {<zoomin_status>,<zoomout_status>,<type>}
#
# After a request to zoomin/out update the display set the type field
# of each node to be the new view for that node (i.e. box, method or
# goal), configure the zoomin/zoomout buttons as appropriate (for
# example, if viewing in box mode then the zoomin button will be
# disabled and the zoomout button enabled). Then refresh the tree.

proc navig_zoom_toggle_cmds {zoomin zoomout type} {
  var_set_node_type $type
  # Set the zoom buttons as appropriate
  [gui_retrieve_window zoom_in] configure -state $zoomin
  [gui_retrieve_window zoom_out] configure -state $zoomout
  # Update the current setting for how all nodes are viewed.
  foreach n [var_retrieve_node_list] {
    var_set_node_value $n type $type
  }
  # Redraw the tree.
  tree_refresh
}

# #############
# GOTO COMMANDS
# #############

# proc navig_goto_root
#
# Shift the tree display so that the root node is visible.

proc navig_goto_root {} {
  # Move the proof display area canvas so that the top center area of
  # the canvas is visible. (xview and yview take as arguments
  # the part of the canvas to view in terms of proportions ranging from
  # 0 to 1 along the x and y axes).
  [gui_retrieve_window pda] yview moveto 0.0
  [gui_retrieve_window pda] xview moveto 0.5
}

# proc navig_goto_current
#
# Shift the tree display so that the current node is visible.

proc navig_goto_current {} {
  if {[var_null_current_node]} {
    navig_goto_root
  } else {
    navig_goto_any [var_retrieve_current_node]
  }
}

# proc navig_goto_user_given
#
# A list of all the nodes in the proof tree is displayed to the
# user. Selection of a node causes the display to shift so that node is 
# visible on screen.

proc navig_goto_user_given {} {
global xb
  set NodeTop .user_node
  destroy $NodeTop
  toplevel $NodeTop
  wm title $NodeTop "Tree Navigation"
  wm geometry $NodeTop +400+400
  $NodeTop configure -bg $xb(bg)
  label $NodeTop.top -text "Select node in tree:" -bg $xb(bg) -fg \
    $xb(fg) -font $xb(font) 
  pack $NodeTop.top -side top -fill x
  set NodeFrame $NodeTop.butts
  frame $NodeFrame
  pack $NodeFrame -side bottom -anchor center
  button $NodeFrame.cancel -fg $xb(fg) -bg $xb(bg) -font $xb(font) \
    -text "Close" -command "destroy .user_node" 
  pack $NodeFrame.cancel -side left
  listbox $NodeTop.choiceList -bg white -fg $xb(fg) -selectforeground \
    white -selectbackground $xb(fg) -font $xb(font) \
    -yscroll "$NodeTop.scroll set" -width 50 
  pack $NodeTop.choiceList -side left -fill both -expand true
  scrollbar $NodeTop.scroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$NodeTop.choiceList yview" -orient \
    vertical -bd 1 -relief sunken 
  pack $NodeTop.scroll -side right -fill y
  # Fill the listbox with the current node addresses, and the names of
  # the methods that have been applied to these (if the node is an open
  # node then just display "open" instead of the method name).
  foreach n [var_retrieve_node_list] {
    set info [var_return_node_value $n method]
    if {$info == {}} {set info [var_return_node_value $n status]}
    $NodeTop.choiceList insert end "$n - $info"
  }
  bind $NodeTop.choiceList <Double-1> {navig_goto_user_any %W %y}
  bind $NodeTop.choiceList <1> {navig_goto_user_any %W %y}
  # Can only delete the window via the Close button
  wm protocol .user_node WM_DELETE_WINDOW {set z 0}
}

# proc navig_goto_user_any
#
# Used to take a node selected by user and alter display so node is on
# screen

proc navig_goto_user_any {Window y} {
  set index [$Window nearest $y]
  set choice [$Window get $index]
  # Strip the address from the users selection
  regexp {[0-9][0-9]*} $choice given_node
  # Now display the node
  navig_goto_any $given_node
}

# proc navig_goto_any
#
# We find the position of the widget that displays the node given in the 
# main window proof display area. We then calculate proportions to find
# out what part of the canvas this widget lies in and orient the canvas
# so that that widget (and thus the node) is visible on the display.
#
# We use proportions since this is required by the canvas "moveto"
# command.
#
# If the proof tree grows extremely big - beyond the defined size of the 
# canvas - then this may not operate.

proc navig_goto_any {given} {
  global Tree
  set pda [gui_retrieve_window pda]
  set curr $pda.text$given
  # Create rectangle enclosing entire canvas
  $pda create rectangle -50c 0c 50c 50c -tags encloser
  # Find bounding box of this rectangle - this saves having to convert
  # between various co-ordinate systems.
  set overall [$pda bbox encloser]
  $pda delete encloser
  # ox1, oy1, ox2, oy2 are the coordinates of the rectangle that bounds
  # the entire proof display area canvas.
  set ox1 [lindex $overall 0]
  set oy1 [lindex $overall 1]
  set ox2 [lindex $overall 2]
  set oy2 [lindex $overall 3]
  # Get the x and y co-ordinates of the node on the canvas
  set midcurrx $Tree($given,x)
  set midcurry $Tree($given,y)
  # midcurrx and midcurry represent a point above and to the left of the 
  # current node. The 300 and 100 are fudge factors but seem to work okay.
  # The if statements handle cases where the node is at the extreme top
  # or left hand side of the defined canvas area.
  set midcurrx [expr $midcurrx + 0.0 - 300]
  if {$midcurrx < $ox1} {
    set midcurrx [expr $ox1 + 1]
  }
  set midcurry [expr $midcurry + 0.0 - 100]
  if {$midcurry < $oy1} {
    set midcurry [expr $oy1 + 1]
  }
  # Find width and height of proof display area canvas.
  set fullx [expr ($ox2 - $ox1)]
  set fully [expr ($oy2 - $oy1)]
  # Find the distance between the left hand edge of the canvas and the
  # node (midcurrx) and the top edge of the canvas and the node
  # (midcurry).
  set midcurrx [expr $midcurrx - $ox1]
  set midcurry [expr $midcurry - $oy1]
  # Calculate the proportion of the distance from the left hand edge of
  # the canvas to the width of the canvas (propx) and the proportion of
  # the distance from the top edge of the canvas to the height of the
  # canvas (propy).
  set propx [expr abs($midcurrx/$fullx)]
  set propy [expr abs($midcurry/$fully)]
  # Shift the view onto the canvas as appropriate so that the area of
  # the canvas in which the current node lies is visible.
  $pda xview moveto $propx
  $pda yview moveto $propy
}
