# ##############################
# ##############################
#
# GLOBAL VARIABLES AND DATATYPES
#
# ##############################
# ##############################

# xb ARRAY - XBARNACLE INFORMATION

global xb

# Default Colours
#
# xb(bg)  - Default background colour.
# xb(fg)  - Default foreground colour.
# xb(abg) - Default active background colour.
# xb(afg) - Default active foreground colour.

set xb(bg) Snow3
set xb(fg) black
set xb(abg) Snow3
set xb(afg) black

# Mouse Cursors
#
# xb(cursor)	 - Default mouse cursor.
# xb(waitcursor) - Mouse cursor that tells the user to wait.

set xb(cursor) {left_ptr Snow1 black}
set xb(waitcursor) {watch black Snow1}

# Current Query Name
#
# xb(query)

proc var_set_current_query {query} {
global xb
  set xb(query) $query
}

proc var_retrieve_current_query {} {
global xb
  return $xb(query)
}


# Current Method Name
#
# xb(method)

proc var_set_current_method {method} {
global xb
  set xb(method) $method
}

proc var_retrieve_current_method {} {
global xb
  return $xb(method)
}

# Current Node
#
# xb(node)

proc var_null_current_node {} {
  if {![string compare [var_retrieve_current_node] "null"]} {
    return 1
  } else {
    return 0
  }
}

proc var_retrieve_current_node {} {
global xb
  return $xb(node)
}

proc var_set_current_node {nid} {
global xb
  set xb(node) $nid
}

proc var_reset_current_node {} {
  var_set_current_node 0
}


# Display Follows Current Node Flag
#
# xb(displayfollow)


# Tracing
#
# xb(trace)        - Default LambdaCLaM trace level.
# xb(trace_window) - Flag indicating if trace window is visible.

proc var_set_trace_level {level} {
global xb
  set xb(trace) $level
}

proc var_retrieve_trace_level {} {
global xb
  return $xb(trace)
}


# Fonts

# if {[catch {set env(FONT)} error]} {
#   set xb(font) -Adobe-Helvetica-Bold-R-Normal--*-120-*-*-*-*-*-*
# } else {
#   set xb(font) $env(FONT)
# }

set xb(font8) -Adobe-Helvetica-Bold-R-Normal--*-80-*-*-*-*-*-*
set xb(font10) -Adobe-Helvetica-Bold-R-Normal--*-100-*-*-*-*-*-*
set xb(font10) -Adobe-Courier-Bold-R-Normal--*-100-*-*-*-*-*-*
set xb(font) -Adobe-Helvetica-Bold-R-Normal--*-120-*-*-*-*-*-*
set xb(font14) -Adobe-Helvetica-Bold-R-Normal--*-140-*-*-*-*-*-*
set xb(font24) -Adobe-Helvetica-Bold-R-Normal--*-240-*-*-*-*-*-*

set xb(fontmaths14) -adobe-symbol-medium-r-normal--8-140-75-75-p-74-adobe-fontspecific
set xb(fontmaths10) -adobe-symbol-medium-r-normal--8-100-75-75-p-74-adobe-fontspecific

set xb(fonttest) $xb(font10)

# Annotations
#
# xb(annotations) - List of types of wave annotation
#                 - if - in front; of - out front; 
#                 - si - sink; wh - wave hole.

# xb(annotations,if) - Names of annotations used for presentation
# xb(annotations,of) - purposes (for example, the ripple key and
# xb(annotations,si) - rippling colour chooser). 
# xb(annotations,wh)
# xb(annotations,if,on) - Dynamic flag whose value can be altered by
# xb(annotations,of,on) - the user. This flag is set if the annotation
# xb(annotations,si,on) - is to be displayed.
# xb(annotations,wh,on)

set xb(annotations) [list if of si wh]
set xb(annotations,if) "In Fronts"
set xb(annotations,of) "Out Fronts"
set xb(annotations,wh) "Wave Holes"
set xb(annotations,si) "Sinks"
set xb(annotations,si,on) 1
set xb(annotations,of,on) 1
set xb(annotations,wh,on) 1
set xb(annotations,if,on) 1

# ################

# colour ARRAY - NODE INFORMATION

global colours

# Annotation Colours
#
# colours(if,fore) etc - Holds the defaults for the foreground and
#                      - background colours of each type of rippling
#                      - annotation. default is used for parts of the
#                      - goal that are not in wave fronts or wave holes
#                        etc.

set colours(default,fore) black
set colours(default,back) white
set colours(if,fore) black
set colours(if,back) green
set colours(of,fore) black
set colours(of,back) goldenrod
set colours(wh,fore) black
set colours(wh,back) white
set colours(si,fore) black
set colours(si,back) cyan

# Available Colours
#
# Colours - List of colour values that the foreground and
#                    - background values of annotations may take

global Colours

set Colours {black white snow bisque cornsilk ivory honeydew azure blue turquoise cyan aquamarine green chartreuse khaki yellow gold goldenrod sienna burlywood wheat tan chocolate firebrick brown salmon orange coral tomato red pink maroon magenta orchid plum purple thistle}

# ################

# node ARRAY - NODE INFORMATION

global node

# General Node Display Information

# Presentation of Nodes
#
# node(type) - A node on the display can be a:
#	     - box: simple shaded block;
#	     - method: shaded box with name of method applied at that
#              node;
#            - goal: shaded box with the name of method applied at that
#              node with the goal at that node with wave annotations
#              shaded.
#
# node(addresses) - Flag indicating whether or not nodes on the display
# should be annotated with their address (if viewing the tree when
# node(type) has value "goal").

proc var_set_node_type {type} {
global node
  set node(type) $type
}

proc var_retrieve_node_type {} {
global node
  return $node(type)
}


# Appearance of a Node.
#
# All distances in pixels.
# 
# node(width,box) - Width of box-type nodes.
# node(height,box) - Height of box-type nodes.
#
# The above are constant for any nodes. The following are dependant
# on the goal and method at a particular node. There will be one
# set of the following for each node on the display, indexed by node 
# address. The first two cases are for when node(type) has value "goal"
# and the second two for when node(type) has value "method". The third
# is for when node(type) has value "box".
#
# node(width,goal,<node id>)  
# node(height,goal,<node id>)	
# node(width,method,<node id>)	
# node(height,method,<node id>)	
# node(width,box,<node id>)	
# node(height,box,<node id>)	
#
# These entries store, in pixels, the width and height of the screen
# space needed to draw the specified node under each of the three
# views.
#
# In addition, each node on display will have one entry as follows,
# again indexed by node address:
#
# node(goaldisp,<node id>) - widget pathname for the textbox component
# 	                   - of the node that holds the annotated
#		           - goal for display. 

set node(width,box) 10
set node(height,box) 10

# Offsets and Distances for Drawing the Tree
#
# All distances in pixels.
#
# node(xoffset)   - X location of the root.
# node(yoffset)   - Y location of the root.
# node(xdistance) - Distance between two side-by-side nodes.
# node(ydistance) - Distance between levels in the tree.

set node(xoffset) 400
set node(yoffset) 10
set node(xdistance) 20
set node(ydistance) 25

# Node Status and Actions Information
#
# node(states) - The possible states of a node (open_status,
#              - partial_status, complete_status, stuck_status).
# node(open_status,prez) etc - The presentational form of this status in 
#                            - the on-screen status key.
# node(open_status,colour) etc - The display colour to be used for nodes
#                              - with this status.
# node(open_status,option) etc - The allowable actions at nodes with
#                              - this status. Values currently include:
#                              - current - set this node to be the 
#                                 node that is planned next.
#                              - goal - view the full goal at this node
#                                 (hypotheses and conclusion and box and
#                                 hole is applicable).
#                              - cut - cut the tree at this node and
#                                 re-plan it.
# node(command,current) etc - The presentational form of this action.

set node(states) {open_status partial_status complete_status stuck_status}

set node(open_status,prez) open
set node(partial_status,prez) partial 
set node(complete_status,prez) complete
set node(stuck_status,prez) stuck 

set node(open_status,colour) DeepSkyBlue1
set node(partial_status,colour) LightSteelBlue1
set node(complete_status,colour) LightSteelBlue3
set node(stuck_status,colour) red

set node(open_status,option) [list goal current]
set node(partial_status,option) [list goal cut]
set node(complete_status,option) [list goal cut]
set node(stuck_status,option) [list goal cut]

set node(command,current) "Current node"
set node(command,goal) "Goal"
set node(command,cut) "Cut tree"

# List of Addresses of Current Nodes in Proof
#
# node(list) DATA-TYPE

# Reset the node(list).

proc var_clear_node_list {} {
global node
  set node(list) {0}
}

# Sort node(list).

proc var_sort_node_list {} {
global node
  set node(list) [lsort $node(list)]
}

# Return the current value of node(list).

proc var_retrieve_node_list {} {
global node
  return $node(list)
}

# Find the position of an address in node(list).

proc var_find_node_list {entry} {
global node
  return [lsearch $node(list) $entry]
}

# Insert in to node(list) the given address, entry.
#
# If index is -1 then add the address to the end of the node(list). Else
# replace the address at position index in node(list) with entry.

proc var_insert_into_node_list {entry {index -1}} {
global node
  if {$index == -1} {
    set node(list) [linsert $node(list) end $entry]
  } else {
    set node(list) [lreplace $node(list) $index $index $entry]
  }
}

# Remove from the node(list) the given address.

proc var_remove_from_node_list {entry} {
global node
  set index [var_find_node_list $entry]
  set node(list) [lreplace $node(list) $index $index]
}


# Information about Each Node in the Proof Tree
#
# node(<node-id>) DATA-TYPE
#
# Each node is indexed by an address and has the following fields:
#
# Status - the status of this node
# Hypotheses
# Conclusion
# Goal
# Method - the method applied to this goal at this node (if any).
# Type - how this node currently is being viewed. As for node(type)
#      - this field can take values goal, method or box.

# Create a node for address.

proc var_new_node {address} {
global node
  set node($address) [list {} {} {} {} {} $node(type)]
}

# Destroy node for address.

proc var_destroy_a_node {address} {
global node
  unset node($address)
}

# Copy address1 node to a new node for address2.

proc var_copy_node {address1 address2} {
global node
  set node($address1) $node($address2)
}

# Return the value of the given field for the specified node.

proc var_return_node_value {address field} {
global node
  switch -- $field {
    status {return [lindex $node($address) 0]}
    hyps {return [lindex $node($address) 1]}
    conc {return [lindex $node($address) 2]}
    goal {return [lindex $node($address) 3]}
    method {return [lindex $node($address) 4]}
    type {return [lindex $node($address) 5]}
  }
}

# Set the value of the given field for the specified node.
# If a new value is given then use this else use a default of {}.

proc var_set_node_value {address field {value {}}} {
global node
  switch -- $field {
    status {set index 0}
    hyps {set index 1}
    conc {set index 2}
    goal {set index 3}
    method {set index 4}
    type {set index 5}
  }
  set node($address) [lreplace $node($address) $index $index $value]
  return $node($address)
}


# ################

global State

# Requests for LambdaCLaM to perform actions are indicated by XBarnacle
# via the variable State.
# is this necessary here ??? Gordon

# proc var_initialise_variables {} {
# draws together several initialisations
# that were scattered through the above file



proc var_initialise_variables {} { 

var_set_current_query "none"
var_set_current_method "top_meth"
var_reset_current_node
set xb(displayfollow) 0
var_set_trace_level 0
set xb(trace_window) 1
var_set_node_type box
set node(addresses) 0
var_clear_node_list
var_new_node 0

}
