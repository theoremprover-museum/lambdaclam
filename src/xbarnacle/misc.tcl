
# ########################
# ########################
#
# MISCELLANEOUS PROCEDURES
#
# ########################
# ########################

# #############################
# SELECTING A NEW QUERY TO PLAN
# #############################

# proc misc_switch_query
#
# Destroy the proof tree and reset the current node to be 0. Reset
# annotation buttons so that all annotations for rippling will be
# displayed. Then tell LambdaCLaM to select the new query.

proc misc_switch_query {theorem} {
  var_set_current_query $theorem
  var_set_current_node 0
  tree_destroy_tree
  annotate_reset_buttons
  var_clear_node_list
  misc_lambda_clam_action new_query
}

# proc misc_plan_new_query
#
# Called from main.pm/xb_handler/2
#
# Set the proof plan to be a single node with the new query then draw
# the tree.

proc plan_new_query {goal} {
  var_new_node 0
  var_set_node_value 0 status open_status
  var_set_node_value 0 hyps ""
  var_set_node_value 0 conc "$goal"
  var_set_node_value 0 goal "$goal"
  tree_construct_nodes 0
  tree_display_tree 
  navig_goto_root
  wm title [gui_retrieve_window toplevel] "X-Barnacle \
    [var_retrieve_current_query]"
}

# ################################################################
# CONVERTING LISTS AND ADDRESSES FROM LAMBDACLAM TO XBARNACLE FORM
# ################################################################

# proc misc_lambda_prolog_to_tcltk_list
#
# Remove all {[]} type brackets from the ends of the list then split the
# list on comma. Finally remove all "'s and return the list. Currently
# this is for MALI-style lists only.

proc misc_lambda_prolog_to_tcltk_list {list} {
  set list [split [string trim $list \[\{\]\}] ,]
  regsub -all \" $list {} list
  return $list
}

# proc misc_lclam_address_to_tcltk
#
# Given LambdaCLaM address of form:
#
# {(a :: (b :: (c :: (d :: nil))))}
#
# convert it to the Tcl/Tk form:
#
# 0[a-1][b-1][c-1][d-1][e-1]
#
# e.g. nil -> 0, (1 :: (3 :: nil)) -> 002 etc

proc misc_lclam_address_to_tcltk {address} {
  set address [split $address ::]
  regsub -all {\(} $address {} address
  regsub -all {\)}  $address {} address
  regsub -all nil $address {} address
  regsub -all \{ $address {} address
  regsub -all \} $address {} address
  set length [llength $address]
  set nuaddress "0"
  for {set i 0} {$i < $length} {incr i} {
    set j [expr [lindex $address $i] - 1]
    set nuaddress "$nuaddress$j"
  }
  return $nuaddress
}

# #############
# USER_FEEDBACK
# #############

# proc misc_user_feedback
#
# Called from main.pm/user_feedback/3.
#
# Display the message in variable args in a location dependant on the
# value of intent.

proc misc_user_feedback {intent args} {
  set info [string trim $args \{\}]
  if {$intent == "info"} {
    misc_display_message "XBarnacle" $info OK
  } elseif {$intent == "trace"} {
    if {$args != ""} {
      trace_add_trace_information $args
    }
  }
}

# ########
# LIB_LOAD
# ########

# proc load_library_file
#
# Retrieve a library file name from the user and then tell LambdaCLaM to 
# load in this file.

proc misc_load_library_file {} {
global LoadFile env
  # This is a Tcl/Tk built-in directory browser command which presents a 
  # browser to the user. When the user has selected a file the command
  # returns this file name.
  set file [exec pwd]
  set file [tk_getOpenFile -title {Load Library File} -initialdir \
  $file/lib]
  if {$file != ""} {
    regsub -all /.*/ $file {} LoadFile
    misc_lambda_clam_action lib_load
  }
}

# Called from main.pm/xb_handler/0

proc misc_retrieve_load_file {} {
global LoadFile
  return $LoadFile
}

# ####
# EDIT
# ####

# proc misc_edit_library_file
#
# Edit a LambdaCLaM library file.

proc misc_edit_library_file {} {
global env
  set file [exec pwd]
  set file [tk_getOpenFile -title {Load Library File} -initialdir \
  $file/lib]
  if {$file != ""} {
    exec $env(EDITOR) $file &
  }
}

# ####
# QUIT
# ####

proc misc_quit_commands {} {
  misc_lambda_clam_action quit
}

# ##########################################
# NODE OPTIONS COMMANDS
# ##########################################

# proc misc_node_option
#
# When the user clicks on a displayed node this procedure is called. The 
# procedure draws at the click-point a pop-up menu with a list of
# actions that can be performed on that node.

proc misc_node_option {nid x y} {
global node xb
  # Retrieve list of actions that can be carried out on this node
  set options $node([var_return_node_value $nid status],option)
  destroy .node_option
  # Create menu
  menu .node_option -type normal -tearoff 0 -relief flat -borderwidth 0
  # Pack in actions allowable on this node - each will trigger a command
  # called misc_opt_<option> (which follow this procedure).
  foreach opt $options { 
    .node_option add command -label $node(command,$opt) -foreground \
    $xb(fg) -background yellow -activeforeground yellow \
    -activebackground black -font $xb(font) -command \
    "destroy .node_option ; misc_opt_$opt $nid" 
  }
  bind .node_option <Leave> "grab release .node_option ; \
    destroy .node_option"
  # Ensure that our behaviours bound to the menu are not done until all
  # other menu behaviours have been executed.
  set menutags [bindtags .node_option]
  set menutags [lreplace $menutags 0 0]
  set menutags [linsert $menutags end .node_option]
  bindtags .node_option $menutags
  # Display the menu and give it focus.
  tk_popup .node_option $x $y
  grab .node_option
}

# proc misc_opt_goal
#
# Display both the hypotheses and conclusion of the goal at the current
# node and display annotations in box and hole form.

proc misc_opt_goal {node_id} {
global xb
  set goal [var_return_node_value $node_id goal]
  set path .goal$node_id
  destroy $path
  toplevel $path
  wm title $path "Node $node_id"
  wm minsize $path 100 200
  $path configure -bg $xb(bg) -height 200 -width 200
  frame $path.butts -bg $xb(bg)
  pack $path.butts -side bottom
  button $path.butts.done -fg $xb(fg) -bg $xb(bg) -font $xb(font) \
    -text "Close" -command "destroy $path" 
  pack $path.butts.done -side bottom
  scrollbar $path.scroll -bg $xb(bg) -command "$path.goal xview" \
    -bd 1 -relief sunken -orient horizontal 
  pack $path.scroll -side bottom -fill x
  scrollbar $path.yscroll -bg $xb(bg) -command "$path.goal yview" \
    -bd 1 -relief sunken  
  pack $path.yscroll -side right -fill y
  canvas $path.goal -width 800 -height 100 -bg white -yscrollcommand \
    "$path.yscroll set" -xscrollcommand "$path.scroll set" \
    -scrollregion {0c 0c 50c 50c} -confine true
  pack $path.goal -fill both -expand 1
  # Insert the goal into the canvas adding graphical representations of
  # any wave annotations.
  annotate_canvas_widget $path.goal $goal
  # On destruction of this window ensure that any tag information
  # relating to annotations or natural fonts is deleted.
  bind $path <Destroy> "annotate_update_tags $path.goal"
}

# proc misc_opt_current
#
# Change the current node to be the selected node.

proc misc_opt_current {node_id} {
  tree_change_node $node_id
  misc_lambda_clam_action current
}

# proc opt_current
#
# Cut the proof tree at the selected node and re-plan this node.

proc misc_opt_cut {node_id} {
  tree_clear_node $node_id
  misc_lambda_clam_action cut
}

# ############################################
# QUERIES - VIEWING AND SELECTING FOR PLANNING
# ############################################

proc misc_view_queries {} {
  misc_queries {Select query to view:} view
}

proc misc_plan_queries {} {
  misc_queries {Select query to Plan:} plan
}

# proc misc_queries
#
# Commands which need list of possible queries call this. Action
# specifies the action to take when the user selects one of the queries
# from the listbox drawn by query_theorem_post (which is entered from
# LambdaProlog).

proc misc_queries {title action} {
global QueryAction QueryTitle
  set QueryTitle $title
  set QueryAction $action
  misc_lambda_clam_action queries
}

# proc misc_queries_post
#
# Called from main.pm/xb_handler/2
#
# Displays a list of the queries currently loaded into
# LambdaCLaM. Selection of one of these calls misc_query_execute with
# the specification of the action to take with the selected query.

proc misc_queries_post {args} {
global xb QueryAction QueryTitle
  set path .query_theorem$QueryAction
  destroy $path
  toplevel $path
  wm title $path $QueryTitle
  $path configure -bg $xb(bg)
  label $path.text -text "Double-click on a query to [string tolower \
    $QueryTitle]" -font $xb(font) -fg $xb(fg) -bg $xb(bg)
  pack $path.text -side top -fill x
  button $path.ok -text "Close" -bg $xb(bg) -fg $xb(fg) -font \
    $xb(font) -command "destroy $path"
  pack $path.ok -side bottom
  listbox $path.list -bg white -fg $xb(fg) -selectforeground \
    white -selectbackground $xb(fg) -font $xb(font) -yscroll \
    "$path.scroll set" -width 50
  pack $path.list -side left -fill both -expand true
  scrollbar $path.scroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$path.list yview" -orient \
    vertical -bd 1 -relief sunken
  pack $path.scroll -side right -fill y
  # Put query names into a listbox
  foreach query [misc_lambda_prolog_to_tcltk_list $args] {
    $path.list insert end [string trim $query \ ]
  }
  bind $path.list <Double-1> \
    "misc_query_execute $QueryAction %W %y ; destroy $path"
}

# proc misc_query_execute
#
# Retrieve a selected query name, and perform the actions specified by
# the name stored in action: "plan" select query for planning, "view"
# select query for viewing.

proc misc_query_execute {action Window Y} {
global Query
  set index [$Window nearest $Y]
  set choice [$Window get $index]
  # This is knowledge of the fact that some LambdaCLaM queries are of
  # form (user_query ...). Ideally XBarnacle should not know this!
  if {[regexp user_query $choice]} {
    set choice [lindex [string trim $choice ()] 1]
  }
  if {$action == "view"} {
    set Query $choice
    misc_lambda_clam_action query
  } elseif {$action == "plan"} {
    misc_switch_query $choice
  }
}

# proc misc_retrieve_query
#
# Called by main.pm/xb_handler/0

proc misc_retrieve_query {} {
global Query
  return $Query
}

# proc misc_query
#
# Called from main.pm/xb_handler/0.
#
# Display the definition of a query.

proc misc_query {name goal} {
global xb
  set path .queryTop$name
  destroy $path
  toplevel $path
  set goal [string trim $goal \"]
  wm title $path "Viewing query $name"
  wm geometry $path +450+450
  frame $path.butt -bg $xb(bg) 
  pack $path.butt -side bottom -fill x
  button $path.butt.cancel -fg $xb(fg) -bg $xb(bg) -cursor $xb(cursor) \
    -font $xb(font) -relief raised -bd 3 -activebackground \
    $xb(abg) -activeforeground $xb(afg) -text "Close" -command \
    "destroy $path"
  pack $path.butt.cancel -side bottom 
  scrollbar $path.yscroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$path.rules yview" -orient \
    vertical -bd 1 -relief sunken -cursor $xb(cursor)
  pack $path.yscroll -side right -fill y
  scrollbar $path.xscroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$path.rules xview" -orient \
    horizontal -bd 1 -relief sunken -cursor $xb(cursor)
  pack $path.xscroll -side bottom -fill x
  text $path.rules -fg black -background white -cursor $xb(cursor) \
    -relief flat -xscrollcommand "$path.xscroll set" \
    -yscrollcommand "$path.yscroll set" -font $xb(font) -wrap none
  pack $path.rules -side left -fill both -expand true
  # On destruction of this window ensure that any tag information
  # relating to annotations or natural fonts is deleted.
  bind $path <Destroy> "annotate_update_tags $path.rules"
  set text_entry "Name: $name\n\n"
  set text_entry "$text_entry   Theorem: $goal"
  annotate_text_widget text $path.rules $text_entry 
  $path.rules configure -state disabled
}

# #############################
# HANDLING SYM_EVAL_RULES_LISTS
# #############################

# proc misc_enable_disable_rewrites
#
# Tell LambdaCLaM to pass to XBarnacle a list of available rewrite rules 
# and a list of those which are currently enabled for rewriting.

proc misc_enable_disable_rewrites {} {
  misc_lambda_clam_action sym_eval_rules_lists
}

# proc misc_Mutual_Rewrite_scroll and misc_Mutual_Rewrite_set
#
# These two procedures are from the Tcl/Tk FAQ and allow two listboxes
# to be mutually scrollable via a single scrollbar

proc misc_Mutual_Rewrite_scroll {path pathlist0 pathlist args} {
  eval $path set $args
  misc_Mutual_Rewrite_set $pathlist0 $pathlist yview moveto \
    [lindex $args 0]
}

proc misc_Mutual_Rewrite_set {pathlist0 pathlist args} {
  eval $pathlist0 $args
  eval $pathlist $args
}

# proc misc_sym_eval_rules_lists
#
# Called from main.pm/xb_handler/0
#
# Display list of all loaded rewrites. Mark those that are enabled for
# use in symbolic evaluation with an X. Allow user double-clicks to
# toggle on and off selected rewrites for use in symbolic evaluation.
#
# all contains the list of all rewrite rules and sym_eval the list of
# those enabled fro rewriting.

proc misc_sym_eval_rules_lists {all sym_eval} {
global xb
  set all [misc_lambda_prolog_to_tcltk_list $all]
  set sym_eval [misc_lambda_prolog_to_tcltk_list $sym_eval]
  set path .add_remove_sym
  destroy $path
  toplevel $path
  wm title $path "Symbolic Evaluation Rules"
  $path configure -bg $xb(bg)
  button $path.ok -text "Close" -bg $xb(bg) -fg $xb(fg) -font \
    $xb(font) -command "destroy $path"
  pack $path.ok -side bottom
  label $path.info -text "X denotes rewrite rules to be used for \
    symbolic evaluation\nDouble-click enables/disables a selected \
    rewrite rule for symbolic evaluation" -bg $xb(bg) -fg $xb(fg) \
    -font $xb(font)
  pack $path.info -side top -fill x
  listbox $path.list0 -exportsel no -bg $xb(bg) -fg $xb(fg) \
    -selectforeground white -selectbackground $xb(fg) -font \
    $xb(font) -yscroll "misc_Mutual_Rewrite_scroll $path.scroll \
    $path.list0 $path.list" -width 1 -relief flat
  pack $path.list0 -side left -fill y
  listbox $path.list -bg white -fg $xb(fg) -selectforeground white \
    -selectbackground $xb(fg) -font $xb(font) -yscroll \
    "misc_Mutual_Rewrite_scroll $path.scroll $path.list0 $path.list" \
    -width 50
  pack $path.list -side left -fill both -expand true
  scrollbar $path.scroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "misc_Mutual_Rewrite_set \
    $path.list0 $path.list yview" -orient vertical -bd 1 -relief sunken
  pack $path.scroll -side right -fill y
  # Go through the list of all rewrite rules
  foreach sym $all {
    # Insert rule name into listbox
    set sym [string trim $sym \ ]
    $path.list insert end $sym
    # If rewrite rule is enabled for rewriting (is in the list sym_eval)
    # then insert an X marker into the other listbox.
    if {[regexp $sym $sym_eval]} {
      $path.list0 insert end "X"
    } else {
      $path.list0 insert end " "
    }
  }
  bind $path.list <Double-1> "misc_Rewrite_add_remove $path %W %y"
  bind $path.list0 <Double-1> "misc_Rewrite_add_remove $path %W %y"
}

# proc misc_Rewrite_add_remove
#
# If a selected rewrite had been enabled for symbolic evaluation then
# call LambdaProlog to de-select it. And vice versa. This includes a
# check to see if the selected rule is user_rewr type rule. The value of
# SymEvalRuleType is set accordingly (technically this is an undesirable 
# way of doing this since it means that XBarnacle has some knowledge of
# the different rewrite rule types!).

proc misc_Rewrite_add_remove {path window y} {
global SymEvalRule SymEvalRuleType SymEvalRuleOp
  set index [$window nearest $y]
  # Get contents of the listbox which displays the X's indicating
  # whether or not a rule is enabled
  set flag [$path.list0 get $index]
  # Get the name of the rewrite rule
  set choice [$path.list get $index]
  # Set SymEvalRuleType to user or system depending on whether or not
  # the selected rewrite rule is a user supplied rewrite rule (of form
  # (user_rewr ...) or not)
  if {[regexp user_rewr $choice]} {
    set choice [lindex [string trim $choice ()] 1]
    set SymEvalRuleType user
  } else {
    set SymEvalRuleType system
  }
  # Get the rule name
  set SymEvalRule [string trim $choice \ ]
  $path.list0 delete $index
  # If the rule was marked as enabled for rewriting then disable it.
  if {[regexp {^X} $flag]} {
    $path.list0 insert $index " "
    set SymEvalRuleOp "remove"
    misc_lambda_clam_action sym_eval_rules
  } else {
    # Else enable it for rewriting.
    $path.list0 insert $index "X"
    set SymEvalRuleOp "add"
    misc_lambda_clam_action sym_eval_rules
  }
}

proc misc_retrieve_sym_eval_rule {} {
global SymEvalRule
  return $SymEvalRule
}

proc misc_retrieve_sym_eval_rule_type {} {
global SymEvalRuleType
  return $SymEvalRuleType
}

proc misc_retrieve_sym_eval_rule_op {} {
global SymEvalRuleOp
  return $SymEvalRuleOp
}


# ############################################
# QUERYING AND CHANGING THE METHOD HIERARCHY
# ############################################

# proc misc_set_top_meth
#
# Gordon : April 2000
# 
# Get a list of methods from Lambda Clam which
# calls misc_compound_methods_post

proc misc_set_top_meth {} {

  misc_lambda_clam_action compound_methods

}

# proc misc_compound_methods_post
#
# Called from main.pm/xb_handler/2
#
# Displays a list of the methods (args) currently loaded in
# LambdaCLaM. Selection of one of these calls misc_method_set
# to set the current method.

proc misc_compound_methods_post {args} {

global xb
  set path .method_chooser
  destroy $path
  toplevel $path
  wm title $path Methods
  .method_chooser configure -bg $xb(bg)
   label $path.text -text "Choose a Method" \
     -font $xb(font) -fg $xb(fg) -bg $xb(bg)

  pack $path.text -side top -fill x
  button $path.ok -text "Close" -bg $xb(bg) -fg $xb(fg) -font \
    $xb(font) -command "destroy $path"
  pack $path.ok -side bottom
  listbox $path.list -bg white -fg $xb(fg) -selectforeground \
    white -selectbackground $xb(fg) -font $xb(font) -yscroll \
    "$path.scroll set" -width 50
  pack $path.list -side left -fill both -expand true
  scrollbar $path.scroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "$path.list yview" -orient \
    vertical -bd 1 -relief sunken
  pack $path.scroll -side right -fill y
  # Put query names into a listbox
  foreach query [misc_lambda_prolog_to_tcltk_list $args] {
    $path.list insert end [string trim $query \ ]
  }
  bind $path.list <Double-1> \
   "misc_method_set %W %y ; destroy $path"
}

# misc_method_set 
#
#

proc misc_method_set {Window Y} {

  set index [$Window nearest $Y]
  var_set_current_method [$Window get $index]

}

# ############################################
# SELECT A REWRITE RULE TO BE A WAVE RULE
# ############################################

# proc misc_choose_wave_rules etc
#
# Gordon: May 2000

# Based on 
# proc misc_enable_disable_rewrites etc
#
# Tell LambdaCLaM to pass to XBarnacle a list of available rewrite rules 
# and a list of those which are currently set as wave_rules

proc misc_choose_wave_rules {} {
  misc_lambda_clam_action wave_rule_lists
}

# proc misc_Mutual_Rewrite_scroll and misc_Mutual_Rewrite_set
#
# These two procedures are from the Tcl/Tk FAQ and allow two listboxes
# to be mutually scrollable via a single scrollbar

proc misc_Mutual_Rewrite_scroll {path pathlist0 pathlist args} {
  eval $path set $args
  misc_Mutual_Rewrite_set $pathlist0 $pathlist yview moveto \
    [lindex $args 0]
}

proc misc_Mutual_Rewrite_set {pathlist0 pathlist args} {
  eval $pathlist0 $args
  eval $pathlist $args
}

# proc misc_wave_rules_lists
#
# Called from main.pm/xb_handler/0
#
# Display list of all loaded rewrites. Mark those that are enabled for
# use in symbolic evaluation with an X. Allow user double-clicks to
# toggle on and off selected rewrites for use in symbolic evaluation.
#
# all contains the list of all rewrite rules and sym_eval the list of
# those enabled fro rewriting.

proc misc_wave_rule_lists {all wave} {
global xb
  set all [misc_lambda_prolog_to_tcltk_list $all]
  set wave [misc_lambda_prolog_to_tcltk_list $wave]
  set path .add_remove_sym
  destroy $path
  toplevel $path
  wm title $path "Wave Rules"
  $path configure -bg $xb(bg)
  button $path.ok -text "Close" -bg $xb(bg) -fg $xb(fg) -font \
    $xb(font) -command "destroy $path"
  pack $path.ok -side bottom
  label $path.info -text "X denotes rewrite rules to be used as\
    wave rules\nDouble-click enables/disables a selected \
    rewrite rule as a wave rule" -bg $xb(bg) -fg $xb(fg) \
    -font $xb(font)
  pack $path.info -side top -fill x
  listbox $path.list0 -exportsel no -bg $xb(bg) -fg $xb(fg) \
    -selectforeground white -selectbackground $xb(fg) -font \
    $xb(font) -yscroll "misc_Mutual_Rewrite_scroll $path.scroll \
    $path.list0 $path.list" -width 1 -relief flat
  pack $path.list0 -side left -fill y
  listbox $path.list -bg white -fg $xb(fg) -selectforeground white \
    -selectbackground $xb(fg) -font $xb(font) -yscroll \
    "misc_Mutual_Rewrite_scroll $path.scroll $path.list0 $path.list" \
    -width 50
  pack $path.list -side left -fill both -expand true
  scrollbar $path.scroll -bg $xb(bg) -activebackground $xb(bg) \
    -troughcolor $xb(bg) -command "misc_Mutual_Rewrite_set \
    $path.list0 $path.list yview" -orient vertical -bd 1 -relief sunken
  pack $path.scroll -side right -fill y
  # Go through the list of all rewrite rules
  foreach sym $all {
    # Insert rule name into listbox
    set sym [string trim $sym \ ]
    $path.list insert end $sym
    # If rewrite rule is enabled as a wave rule (is in the list wave)
    # then insert an X marker into the other listbox.
    if {[regexp $sym $wave]} {
      $path.list0 insert end "X"
    } else {
      $path.list0 insert end " "
    }
  }
  bind $path.list <Double-1> "misc_Wave_add_remove $path %W %y"
  bind $path.list0 <Double-1> "misc_Wave_add_remove $path %W %y"
}

# proc misc_Rewrite_add_remove
#
# If a selected rewrite had been enabled as a wave rule then
# call LambdaProlog to de-select it. And vice versa. This includes a
# check to see if the selected rule is user_rewr type rule. The value of
# WaveRuleType is set accordingly (technically this is an undesirable 
# way of doing this since it means that XBarnacle has some knowledge of
# the different rewrite rule types!).

proc misc_Wave_add_remove {path window y} {
global WaveRule WaveRuleType WaveRuleOp
  set index [$window nearest $y]
  # Get contents of the listbox which displays the X's indicating
  # whether or not a rule is enabled
  set flag [$path.list0 get $index]
  # Get the name of the rewrite rule
  set choice [$path.list get $index]
  # Set WaveRuleType to user or system depending on whether or not
  # the selected rewrite rule is a user supplied rewrite rule (of form
  # (user_rewr ...) or not)
  # Gordon - look at this for Wave Rules
  if {[regexp user_rewr $choice]} {
    set choice [lindex [string trim $choice ()] 1]
    set WaveRuleType user
  } else {
    set WaveRuleType system
  }
  # Get the rule name
  set WaveRule [string trim $choice \ ]
  $path.list0 delete $index
  # If the rule was marked as enabled for rewriting then disable it.
  if {[regexp {^X} $flag]} {
    $path.list0 insert $index " "
    set WaveRuleOp "remove"
    misc_lambda_clam_action wave_rules
  } else {
    # Else enable it for rewriting.
    $path.list0 insert $index "X"
    set WaveRuleOp "add"
    misc_lambda_clam_action wave_rules
  }
}

proc misc_retrieve_wave_rule {} {
global WaveRule
  return $WaveRule
}

proc misc_retrieve_wave_rule_type {} {
global WaveRuleType
  return $WaveRuleType
}

proc misc_retrieve_wave_rule_op {} {
global WaveRuleOp
  return $WaveRuleOp
}








# ############################################
# REQUESTING THAT LAMBDACLAM PERFORM AN ACTION
# ############################################

# These procedures allow XBarnacle (and by extension user actions) to
# cause actions to occur in LambdaCLaM.

# proc misc_lambda_clam_action
#
# Alter the value of global variable State to be the given value.

proc misc_lambda_clam_action {state} {
  global State
  set State $state
}

# proc misc_poll_user_event
#
# Called from plan.pm/execute_command/0.
#
# Using the tkwait command poll the value of State. When its value
# alters then return the value (to LambdaCLaM).

proc misc_poll_user_event {} {
  global State
  tkwait variable State
  return $State
}

# proc misc_polled_user_event
#
# Return the current value of state.

proc misc_polled_user_event {} {
global State
  return $State
}

# ###################
# DISPLAYING MESSAGES
# ###################

# proc display_message
#
# Display a message (with appropriate icon in dialog box). buttons is a
# list of buttons. This procedure will return the name of the button
# that was selected by the user.

proc misc_display_message {title message buttons} {
  set command "tk_dialog .message {$title} {$message} info 0"
  foreach button $buttons {
    set command "$command {$button}"
  }
  set chosen [eval $command]
  return [lindex $buttons $chosen]
}

# proc display_error
#
# Display an error message (with appropriate icon in dialog box).

proc misc_display_error {error_message} {
  tk_dialog .error "XBarnacle Problem!" $error_message error 0 OK
}

# proc misc_xbify_dialog
#
# As XBarnacle makes use of some built-in procedures for drawing dialog
# boxes and file browsers. The following allow the display of such
# interface components using XBarnacle colours and fonts rather than
# default ones of Tcl/Tk 8.0.

proc misc_xbify_dialog {window} {
global xb
  set class [winfo class $window]
  if {($class == "Listbox") || ($class == "Canvas")} {
    set colour white
  } else {
    set colour $xb(bg)
  }
  catch {$window configure -bg $colour}
  catch {$window configure -fg $xb(fg)}
  catch {$window configure -font $xb(font)}
  # Recurse down the widget hierarchy to ensure that all widgets that
  # make up the dialog box are coloured appropriately.
  foreach child [winfo children $window] {
    misc_xbify_dialog $child
  }
}

proc misc_lclam_interactive {} {

   misc_lambda_clam_action nothing
 
}
# Bind a call to misc_xbify_dialog to the event of displaying of dialog
# boxes.

bind Dialog <Map> {misc_xbify_dialog %W}
bind TkFDialog <Map> {misc_xbify_dialog %W}
