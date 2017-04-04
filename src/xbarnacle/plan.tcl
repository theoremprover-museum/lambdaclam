# ########
# ########
# 
# PLANNING
#
# ########
# ########

# Play GLOBAL VARIABLE
#
# Play variable is set if XBarnacle/LambdaCLaM is to do proof steps
# until ordered to stop by the user.

# global Play
# set Play 0

# ########################################
# UPDATING THE PROOF AFTER A PLANNING STEP
# ########################################

# proc plan_update_planned_node
#
# Called from plan.pm/update_ui_node_parent/4.
#
# Called from plan.pm with information about the new state of the
# planned node. NerwChildren will hold a (possibly empty) list of the
# addressess of the children of this node resulting from its planning.

proc plan_update_planned_node {name address method status goal hyps conc} { 
global NewChildren
set rewrite ""
  # Convert address to Tcl/Tk format
  set address [misc_lclam_address_to_tcltk $address]
  # If replanning an already planned node...
  if {[var_return_node_value $address status] == "partial_status" || \
    [var_return_node_value $address status] == "complete_status"} {
    tree_clear_node $address
  }
  # Save status
  var_set_node_value $address status $status
  # This should be done in LambdaCLaM (these method names usually
  # contain the list of rewrite rules as an argument!)
  if {[regexp sym_eval $method]} {
    set method sym_eval
  } elseif {[regexp {rewrite_with [^ \.]*} $method rewrite]} {
    set method $rewrite
  }
  # Save method name
  var_set_node_value $address method $method
  # Update the displayed version of this node
  tree_update_node $address
  # Mark that there is no current node for now
  var_set_current_node null
  set NewChildren [list]
}

# proc plan_create_child_node
#
# Called from plan.pm/update_ui_node_child/3.
#
# Save the information for a new node and save the
# address of this new node in the NewChildren list.

proc plan_create_child_node {name address status goal hyps conc} {
global NewChildren
  set address [misc_lclam_address_to_tcltk $address]
  set NewChildren [linsert $NewChildren end $address]
  # Add address to list of nodes
  var_insert_into_node_list $address
  # Create new node and update it using the status, hypotheses,
  # conclusion, goal, method and the current way in which nodes are to
  # be displayed (box, method or goal).
  var_new_node $address
  var_set_node_value $address status $status
  var_set_node_value $address hyps "$hyps"
  var_set_node_value $address conc "$conc"
  var_set_node_value $address goal "$goal"
  var_set_node_value $address method
  var_set_node_value $address type [var_retrieve_node_type]
  # Set this node to be the current node
  var_set_current_node $address
}

# proc plan_update_proof_plan
#
# Called from plan.pm/update_ui/3.
#
# Updates the proof after planning a node. This includes setting a
# setting a node to be the new current node; adding nodes on the display
# for any new nodes in the plan; updating the status of each node in the 
# proof tree; and adjusting the view onto the proof tree.

proc plan_update_proof_plan {} {
global xb NewChildren
  # Sort the list of nodes
  var_sort_node_list
  foreach n [var_retrieve_node_list] {
    # Set the first open node in the node list to be the current node
    if {([var_return_node_value $n status] == "open_status") && \
        ([var_null_current_node])} {
      var_set_current_node $n
    }
  }
  # Update status of nodes in proof tree
  plan_update_status 0
  set xbnode 0
  # Create display nodes for each new child node. Use xbnode to
  # set the first child node created to be the new current node
  foreach i $NewChildren {
    if {[var_return_node_value $i status] == "open_status" && \
      $xbnode == 0} {
      var_set_current_node $i
      set xbnode 1
    }
    tree_destroy_node $i
    tree_node_build $i
  }
  # Redraw tree
  tree_refresh
  # If current node is to always be visible on display then shift
  # the displayed area of the proof as appropriate
  if {$xb(displayfollow) && ![var_null_current_node]} {
    navig_goto_any $xb(node)
  }
}

# proc plan_update_status
#
# If all the children of a node are complete then set the status of this 
# node to complete (recurses on the child nodes first). May be used to
# update status of every node on the tree

proc plan_update_status {nid} {
  set children [tree_get_children $nid]
  foreach child $children {plan_update_status $child}
  set compl 1
  foreach child $children {
    if {[var_return_node_value $child status] != "complete_status"} {
      set compl 0}
  }
  if {$compl} {
    if {[llength $children] != 0} {
      var_set_node_value $nid status "complete_status"
    }
  }
}

# ##################################################
# ENSURING BUTTON STATES ARE CORRECT DURING PLANNING
# ##################################################

# proc plan_set_buttons_during_planning
#
# Either all buttons are disabled except the pause button (for cases
# when the user is playing a proof), or all buttons are active and the
# pause button is disabled (for when the user is single-stepping through
# the proof).

proc plan_set_buttons_during_planning {statepause stateothers} {
global xb
  [gui_retrieve_window play] config -fg $xb(fg) -state $stateothers
  [gui_retrieve_window step] config -fg $xb(fg) -state $stateothers
  [gui_retrieve_window back] config -fg $xb(fg) -state $stateothers
  [gui_retrieve_window stop] config -fg $xb(fg) -state $stateothers
  [gui_retrieve_window pause] config -fg $xb(fg) -state $statepause
  [gui_retrieve_window pda] config -cursor watch
}

# proc plan_set_buttons_not_planning
#
# Play and step buttons are enabled and the rest are disabled.

proc plan_set_buttons_not_planning {} {
global xb
  [gui_retrieve_window play] config -fg $xb(fg) -state normal
  [gui_retrieve_window step] config -fg $xb(fg) -state normal
  [gui_retrieve_window back] config -fg $xb(fg) -state disabled
  [gui_retrieve_window stop] config -fg $xb(fg) -state disabled
  [gui_retrieve_window pause] config -fg $xb(fg) -state disabled
  [gui_retrieve_window pda] config -cursor top_left_arrow
}

# proc plan_adjust_planning_menus_states
#
# Disable/enable these menus during/after planning.

proc plan_adjust_planning_menus_states {state} {
  [gui_retrieve_window menu_File] configure -state $state
  [gui_retrieve_window menu_View] configure -state $state
  [gui_retrieve_window menu_Plan] configure -state $state
  [gui_retrieve_window menu_Rewrites] configure -state $state
}

# ####################
# CONTROLLING PLANNING
# ####################

# proc plan_continue_planning
#
# Called from plan.pm/ui_continue_or_intervene/4.
#
# If Play is set then just carry out the last user proof-related action
# again (which, by definition of the condition under which Play will
# have been set, will be a request to perform a proof step).
# Else, wait until the user performs some action related to the proof.
# the proof. 

proc plan_continue_planning {} {
global State Play
  if {$Play} {
    misc_polled_user_event
  } else {
    misc_poll_user_event
  }
}

# proc plan_stop_commands
#
# Check if the user wants to abandon the proof. If so then tell
# LambdaCLaM to do this.

proc plan_stop_commands {} {
  set abandon [misc_display_message "Abandon Proof" "Abandon this proof \
    attempt ?" {No Yes}]
  if {$abandon == "Yes"} {
    misc_lambda_clam_action abandon
  }
}

# proc plan_pause_commands
#
# If the proof is playing automatically then stop this and update the
# proof control buttons as appropriate.

proc plan_pause_commands {} {
global Play
  set Play 0
  plan_set_buttons_during_planning disabled normal
}

# proc plan_back_commands
#
# Tell LambdaCLaM to backtrack.

proc plan_back_commands {} {
  misc_lambda_clam_action backtrack
}

# proc plan_step_commands
#
# Tell LambdaCLaM to perform one proof step.

proc plan_step_commands {} {
global Play
  set Play 0
  plan_proof_step
}

# proc plan_play_commands
#
# Tell LambdaCLaM to perform one proof step and set Play to 1 to ensure
# that playing continues until the user pauses the proof.

proc plan_play_commands {} {
global Play
  set Play 1
  plan_proof_step
}

# proc plan_proof_step
#
# Check if a query has been selected for planning. If so then tell
# LambdaCLaM to perform a proof step (after having enabled/disabled the
# planning control buttons as appropriate).

proc plan_proof_step {} {
global Play
  if {[var_retrieve_current_query] == "none"} {
    misc_display_error "First, select a query to prove."
    set Play 0
  } else {
    plan_adjust_planning_menus_states disabled
    if {$Play == 1} { 
      plan_set_buttons_during_planning normal disabled 
    } else {
      plan_set_buttons_during_planning disabled normal
    }
    misc_lambda_clam_action dplan_method
  }
}

##########################
# PLANNING SUCCESS/FAILURE
##########################

# proc plan_complete_planning
#
# Called from main.pm/planning_success/0 and 
#             main.pm/planning_failure/0
#
# Notify user as to whether planning succeeded or failed.

proc plan_complete_planning {theorem result} {
  if {$result == "fail"} {
    set info "Failed to prove $theorem."
  } else {
    set info "Proved $theorem."
  }
  misc_display_message "XBarnacle" $info {OK}
  plan_adjust_planning_menus_states normal
  plan_set_buttons_not_planning
}
