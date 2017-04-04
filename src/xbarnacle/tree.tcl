################
################
#
# THE PROOF TREE
#
################
################

# When a node is to be drawn on screen some new entries of the node
# array are calculated. This calculation is done by tree_node_build. 
#
# There will be one set of the following entries for each node intended
# for display, indexed by node addresses. Each entry contains the width
# and height needed to display the node under each of the three views of 
# the proof tree (goal view, in which the goal and the method applied to
# the goal is displayed, method view, in which just the method is
# displayed, and box view in which just a simple block is shown):
#
# node(width,goal,<node id>)  
# node(height,goal,<node id>)
# node(width,method,<node id>)
# node(height,method,<node id>)
# node(width,box,<node id>)
# node(height,box,<node id>)
#
# In addition, each node on display will have one entry as follows,
# again indexed by node address:
#
# node(goaldisp,<node id>)
#
# This holds a widget pathname for a textbox which holds the goal.

# tree_calculate_width and tree_calc_tree are used to calculate how the
# tree as a whole is laid out. These procedures make use of the width
# and height information in the node array entries as above to build a
# Tree array. This holds the following entries:
#
# Tree(<node id>,x)
# Tree(<node id>,y)
#
# These are the x and y coordinates where the node with address <node
# id> will be drawn.
#
# Tree(<node id>,space)
#
# This holds an number denoting the number of pixels that should be left 
# empty beneath this node.
#
# Tree(all,correction)
#
# This is a general entry and holds the number of pixels to add or
# subtract from all x coordinates to make the root of the tree stay on
# the same place of the canvas 

# Some operations, for example adding a new node require building width, 
# height and goaldisp entries for that node and then recalculating the
# Tree array before redrawing the tree. Other operations however, for
# example changing the view of a node or the whole tree just require
# recalculation of the Tree array. Hence there are a number of varieties 
# of tree destructor and redrawing operations. For example:
#
# Changing the view of the tree between box/method/goal: since the node
# information above will have been calculated we just destroy the node
# widgets on the screen, recalculate the Tree array in light of our view 
# change and redraw the tree. 
#
# Changing current node: since this only involves altering the
# borderwidth of the node that is now the current node and the
# borderwidth of the node that was the current node we can just delete
# and redraw these two nodes without having to touch the node or Tree
# arrays. 
#
# Cutting the proof tree: since we could jump back to a significantly
# different proof state this involves clearing the node at which the cut 
# is requested and resetting it to an open node. The branch beneath this
# node must then be completely removed and then the node and Tree array
# entries recalculated.
#
# Planning a node: first we must cut the tree as above (since we could
# have backtracked to this node) then we just recalculate the node width
# entries in the node array.
#
# For adding new nodes: we destroy any nodes already with the same
# address then build new entries in the node array for the width, height
# and textbox widget information.
#
# After having planned a node: we refresh the whole tree, to recalculate 
# the Tree array contents, and then redraw the tree.

# #########################################
# RETRIEVE INFORMATION ABOUT THE PROOF TREE
# #########################################

# proc tree_get_children
#
# Return the addresses of the children of the node with address nid.

proc tree_get_children {nid} {
  set result {}
  foreach n [var_retrieve_node_list] {
    # Check if nid is prefix to n and n is exactly one character longer
    # than nid. If so, then n is a child of nid.
    if {[regexp ^$nid.$ $n]} {
      lappend result $n
    }
  }
  return $result
}

# proc tree_get_descendants
#
# Return the addresses of the descendants of the node with address nid.

proc tree_get_descendants {nid} {
  set result {}
  foreach n [var_retrieve_node_list] {
    # Check if nid is the prefix of n. If so then n is a descendant of
    # nid
    if {[regexp ^$nid $n]} {
      lappend result $n
    }
  }
  return $result
}
 
# proc tree_get_level {<node_address>}
#
# From the address of a node calculate its depth in the tree.

proc tree_get_level {nid} {
  return [string length $nid]
}

# proc tree_get_nodes_on_level {<depth>}
#
# Return a list of the addresses of all nodes at depth level in the
# tree.

proc tree_get_nodes_on_level {depth} {
  set list {}
  foreach id [var_retrieve_node_list] {
    if {[string length $id] == $depth} {lappend list $id}
  }
  set list [lsort -increasing $list]
  return $list
}

# #########################
# CHANGING THE CURRENT NODE
# #########################

# proc tree_change_node
#
# Change the display to indicate that the node with address nodeid
# is now the current node. There is no need to recalculate the widths or 
# heights in the node array or to recalculate the Tree array since we
# are in effect just changing the border widths of two nodes.

proc tree_change_node {nodeid} {
global Tree
  # Delete widget for current node
  [gui_retrieve_window pda] delete currentnode
  # Delete widget for selected node
  [gui_retrieve_window pda] delete node$nodeid
  # Update current node
  set oldcurrent [var_retrieve_current_node]
  var_set_current_node $nodeid
  # Redraw old current node in the same position as it was before
  tree_draw_node $oldcurrent $Tree($oldcurrent,x) $Tree($oldcurrent,y)
  # Redraw the node that is now the current node in the same 
  # position as it was before
  tree_draw_node [var_retrieve_current_node] \
    $Tree([var_retrieve_current_node],x) \
    $Tree([var_retrieve_current_node],y)
}

# ##########################################################
# SET A NODE TO BE AN OPEN NODE (USED TO SUPPORT A TREE CUT)
# ##########################################################

# proc tree_clear_node_from_prolog
#
# Called from plan.pm/ui_clear_tree/2.
#
# Delete the branch under the node with the given address after
# converting the given address into the XBarnacle form.

proc tree_clear_node_from_prolog {PrologAddress} {
  set address [misc_lclam_address_to_tcltk $PrologAddress]
  tree_clear_node $address
}

# proc tree_clear_node
#
# Delete the branch under the node with the given address. Then set the
# node with the given address to be an open node.

proc tree_clear_node {address} {
global node
  tree_delete_branch $address
  var_set_node_value $address status open_status
  var_set_node_value $address hyps [var_return_node_value $address hyps]
  var_set_node_value $address conc [var_return_node_value $address conc]
  var_set_node_value $address goal [var_return_node_value $address goal]
  var_set_node_value $address method
  var_set_node_value $address type $node(type)
  destroy_then_display_tree
}

# proc tree_delete_branch
#
# Delete the branch rooted at the given node. Do not delete the given
# node however.

proc tree_delete_branch {nid} {
  foreach n [var_retrieve_node_list] {
    if {[string first $nid $n] == 0 && \
      [string length $nid] < [string length $n]} {
      tree_destroy_node $n
      # Remove node from list of nodes in tree
      var_remove_from_node_list $n
    }
  }
  # Update status of ancestors of node at which branch was delected
  tree_update_parents_after_delete $nid "open_status"
  # Set current node to be node at which branch was cut
  var_set_current_node $nid
}

# proc tree_update_parents_after_delete
#
# After cutting a branch of the tree reset the status of all nodes above 
# the node at which the cut was performed to partial_status. Set the
# status of the node at which the tree was cut to the given status
# (usually open_status).

proc tree_update_parents_after_delete {nid status} {
  var_set_node_value $nid status $status
  set parent [string range $nid 0 [expr [string length $nid] - 2]]
  # Check we have not reached the root.
  if {$parent != ""} {
    tree_update_parents_after_delete $parent "partial_status"
  }
}

#######################################
# DRAWING NODES AND DISPLAYING THE TREE
#######################################

# proc tree_display_tree
#
# Calculate the space required for nodes then display the proof
# tree. This assumes that the node array contains the goaldisp entries
# holding the textbox widgets for goals and the width and height
# information concerning each node.

proc tree_display_tree {} {
  # Calculate space needed to draw each node neatly
  tree_calculate_width 0
  # Calculate where arcs should go and finish off laying out tree
  tree_calc_tree 0 0
  # Draw the root note - by definition of tree_draw this will draw all
  # other nodes first
  tree_draw 0
}

# proc tree_refresh
#
# Destroy all the widgests on the tree then re-display the tree. As for
# the above it assumes that the node array contains the goaldisp entries
# holding the textbox widgets for goals and the width and height
# information concerning each node.

proc tree_refresh {} {
  tree_destroy_widgets
  tree_display_tree
}

# proc destroy_then_display_tree
# 
# Re-calculate and redraw the tree (used for example when redisplaying
# tree after toggling on node address information)

proc destroy_then_display_tree {} {
  tree_destroy_tree
  tree_construct_nodes 0
  tree_display_tree
}

# proc tree_draw
#
# Draw the children of a given node then draw the node. Can be used to
# draw the whole tree if nid is 0 (the root node). Information in the
# Tree array is used to specify where each node should be drawn. This
# assumes that the node array and Tree arrays are up to date and that
# all heights, widths, x and y coordinates have been calculated.

proc tree_draw {nid} {
global Tree
  set children [tree_get_children $nid]
  foreach child $children {
    tree_draw $child
  }
  tree_draw_node $nid $Tree($nid,x) $Tree($nid,y)
}

# proc tree_draw_node
#
# This procedure actually adds a node to the canvas, displaying the
# appropriate information and binding behaviours to it.
#
# It draws a rectangle shaded dependant upon the status of the node.
# Then, depending upon how the node is to be viewed, it adds the method
# name, and the textbox containing the goal (which is stored in the
# node(goaldisp,<nid) entry of the node array.

proc tree_draw_node {nid x y} {
global node xb Tree
  set canvas [gui_retrieve_window pda]
  set width $node(width,[var_return_node_value $nid type],$nid)
  set height $node(height,[var_return_node_value $nid type],$nid)
  set x1 [expr $x-($width/2)]
  set y1 [expr $y-($height/2)]
  set x2 [expr $x+($width/2)]
  set y2 [expr $y+($height/2)]
  # Create a shortcut tag to access the shaded rectangle that forms the
  # node as a whole.
  if {([string compare $xb(node) $nid] == 0) && \
    ([string length $xb(node)] == [string length $nid])} {
    set width 3
    set TagToUse currentnode
  } else {
    set width 1
    set TagToUse node$nid
  }
  # Get the colour (dependant on status of node)
  set colour $node([var_return_node_value $nid status],colour)
  # Create the rectangle
  set id [$canvas create rectangle  $x1 $y1 $x2 $y2 -fill $colour \
    -outline black -width $width -tag $TagToUse]
  switch -- [var_return_node_value $nid type] {
    goal {
      # Add the textbox that holds the goal
      $canvas create window $x [expr $y - (($y-$y1)/2)] \
        -window $node(goaldisp,$nid) 
      # Display address with node if this option is enabled
      if {$node(addresses)} {
        $canvas create text $x1 [expr $y1 - 12] -text $nid \
          -anchor nw -font $xb(font10)]
     }
         # Add method name
        set name_id [$canvas create text $x [expr $y + (($y-$y1)/2)] \
          -text [var_return_node_value $nid method]]
        # If click on method name then pop-up menu displaying actions
        # available at that node will appear
        $canvas bind $name_id <1> "misc_node_option $nid %X %Y"
        $canvas bind $name_id <2> "navig_resize_option $nid"
        $canvas bind $name_id <3> "navig_resize_branch_option $nid"
      }
    method {
        # Add method name
        set name_id [$canvas create text $x $y \
          -text [var_return_node_value $nid method]]
        # If click on method name then pop-up menu displaying actions
        # available at that node will appear
        $canvas bind $name_id <1> "misc_node_option $nid %X %Y"
        $canvas bind $name_id <2> "navig_resize_option $nid"
        $canvas bind $name_id <3> "navig_resize_branch_option $nid"
    }
    default {
    }
  }
  # If click on the node then pop-up menu displaying actions
  # available at hat node will appear
  $canvas bind $TagToUse <1> "misc_node_option $nid %X %Y"
  $canvas bind $TagToUse <2> "navig_resize_option $nid"
  $canvas bind $TagToUse <3> "navig_resize_branch_option $nid"
}

########################
# PROOF TREE DESTRUCTORS
########################

# proc tree_destroy_widgets
#
# Delete every widget within the proof display area.

proc tree_destroy_widgets {} {
  [gui_retrieve_window pda] delete all
}

# proc tree_destroy_node
#
# Remove the widgets for this node. This destroys the textboxes used to
# hold the goal for each widget that was built by the tree_build_node
# procedure. Then remove its tag information indicating that this widget 
# no longer exists.

proc tree_destroy_node {nodeid} {
global node
  catch {destroy $node(goaldisp,$nodeid)}
  catch {annotate_update_tags $node(goaldisp,$nodeid)}
}

# proc tree_destroy_tree
#
# Delete all the nodes using tree_destroy_node then destroy all the
# widgets in the proof display area.

proc tree_destroy_tree {} {
  foreach n [var_retrieve_node_list] {
    tree_destroy_node $n
  }
  tree_destroy_widgets
}

###################################
# CREATING NODES FOR THE PROOF TREE
###################################

# proc tree_construct_nodes
#
# Given a node address create the node array elements necessary for this 
# node to be displayed on screen (i.e. a textbox widget for the goal and
# width and height information for each view). Calculate the information
# for the children of the node first.

proc tree_construct_nodes {nid} {
global Tree
  set children [tree_get_children $nid]
  foreach child $children {
    tree_construct_nodes $child
  }
  tree_node_build $nid
}

# proc tree_node_build
#
# Create a text widget to go on the canvas for displaying the given
# node, adding method and colour the annotations. Also store width and
# height information to be used when calculating how to layout the nodes
# to form the tree

proc tree_node_build {nid} {
global node xb
  set canvas [gui_retrieve_window pda]
  set con ""
  # Get the conclusion of the goal at node nid
  set con [var_return_node_value $nid conc]
  regsub -all {\*} $con { } con
  # Define a textbox for the goal and save the pathname of this widget
# JULIANR - FONT
  set node(goaldisp,$nid) [text $canvas.goal$nid -height 1 -fg black \
      -bg white]
  bindtags $node(goaldisp,$nid) .
  # Set width of goal textbox to be 1 character longer than the name of
  # the method applied at the node
  $node(goaldisp,$nid) config \
      -width [expr [string length [var_return_node_value $nid method]] -1]
  # Get the length and height of the textbox in pixels
  set methwdth [winfo reqwidth $node(goaldisp,$nid)]
  set methheight [winfo reqheight $node(goaldisp,$nid)]
  # Insert the conclusion into the textbox and calculate annotation
  # information and natural font information
  annotate_text_widget node $node(goaldisp,$nid) $con
  # Get the contents of the textbox (since the call to
  # annotate_text_widget will have altered the contents)
  set text [$node(goaldisp,$nid) get 1.0 end]
  # Set the textbox to be the width of the new contents
  $node(goaldisp,$nid) config -width [expr [string length $text] -1]
  # Set the width to use for the node when viewing in method view to be
  # just larger than the width required to display the method name
  set node(width,method,$nid) [expr $methwdth + 4]
  # Set the width to use for the node when viewing in goal view to be
  # the larger of (width required to display conclusion, width required
  # to display method).
  if {$methwdth > [winfo reqwidth $node(goaldisp,$nid)]} {
    set node(width,goal,$nid) [expr $methwdth + 4]
  } else {
    set node(width,goal,$nid) \
        [expr [winfo reqwidth $node(goaldisp,$nid)] + 4]
  }  
  # Set the width and height to use for displaying in box view to be the 
  # defaults
  set node(width,box,$nid) $node(width,box)
  set node(height,box,$nid) $node(height,box)
  # Set the height required to view the node in method and goal views.
  set node(height,goal,$nid) \
      [expr ([winfo reqheight $node(goaldisp,$nid)] * 2)+2]
  set node(height,method,$nid) [expr $methheight + 4]
  # Prevent user from altering contents of the conclusion textbox
  $node(goaldisp,$nid) config -state disabled
}

# proc tree_update_node
#
# This is a short form of the above used to update the information
# stored about a node. This is used when an open node has been planned
# and we need to recalculate the width and height that the node needs to 
# be when displaying the node in method view. The temporary widget .temp
# is used to assist in calculation - so we can get pixel distances.

proc tree_update_node {nid} {
global node
  text .temp -height 1
  .temp config -width [expr [string length [var_return_node_value $nid method]] -1]
  set methwdth [winfo reqwidth .temp]
  set methheight [winfo reqheight .temp]
  set node(width,method,$nid) [expr $methwdth + 4]
  set node(height,method,$nid) [expr $methheight + 4]
  if {$methwdth > [winfo reqwidth $node(goaldisp,$nid)]} {
    set node(width,goal,$nid) [expr $methwdth + 4]
  } else {
    set node(width,goal,$nid) \
        [expr [winfo reqwidth $node(goaldisp,$nid)] + 4]
  }  
  destroy .temp
}

# ##################################################################
# PROCEDURES FOR CALCULATING THE SPACE NEEDED FOR NODES AND THE TREE
# ##################################################################

# proc tree_calc_tree
#
# This calculates where each node should go in the display and also
# draws the arcs between the nodes.

proc tree_calc_tree {nid offset} {
global Tree node Yc
  if {([string compare $nid 0] == 0) && ([tree_get_level $nid] == 1)} {
    set Tree(all,correction) \
      [expr $node(xoffset)-($offset+([expr $Tree($nid,space)]/2))]
    set Tree($nid,x) $node(xoffset)
  } else {
    set Tree($nid,x) [expr $offset+([expr \
    $Tree($nid,space)]/2)+$Tree(all,correction)]
  }
  set level [tree_get_level $nid]
  set height $node(height,goal,$nid)
  set Yc($level) [expr $node(yoffset) + (($height / 2) + \
      (([tree_get_level $nid] - 1)*($height+$node(ydistance))))]
  set Tree($nid,y) $Yc($level)
  set children [tree_get_children $nid]
  foreach child $children {
    tree_calc_tree $child $offset
    set offset [expr $offset+$Tree($child,space)]
    [gui_retrieve_window pda] create line  $Tree($nid,x) $Tree($nid,y) \
    $Tree($child,x) $Tree($child,y) -fill black -width 1
  }
}

# tree_calculate_width {<node_address>}
#
# Calculate how many pixels-width of the proof display area canvas is
# needed to display the sub-tree rooted at the node with the given
# address.
#
# The width is stored in Tree(<node_address>,space).

proc tree_calculate_width {nid} {
global Tree node
  set children [tree_get_children $nid]
  set space 0
# Sum the widths required for the sub-trees rooted at each of the
# child nodes of node nid
  foreach child $children {
    set space [expr $space + [tree_calculate_width $child]]
  }
# Retrieve the pixel-width required to display the node nid - this is
# determined by how the node is being viewed on the display (as a box,
# a method or a full method and goal combination).
  set width $node(width,[var_return_node_value $nid type],$nid)
# Find the maximum of (width required for node,width required for
# sub-trees of children of current node) and set this to be the width
# required to display the sub-tree rooted at the node nid.
  if {$space < $width} {
    set Tree($nid,space) [expr ($width + $node(xdistance))]
  } else {
    set Tree($nid,space) $space
  }
  return $Tree($nid,space)
}
