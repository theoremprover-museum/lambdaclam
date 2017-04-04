# ####
# ####
#
# HELP
#
# ####
# ####

# Procedures for balloon help and general help on-line also.

global Balloon
set Balloon(balloon,first) 0
set Balloon(balloon,set) 0
set Balloon(balloon,soon) 0
set Balloon(pr,balloon) 1

# This public domain code has been slightly altered so make use
# of XBarnacle colour schemes and fonts

##############################################################################
# $Id: help.tcl,v 1.1.1.1 2006/09/05 09:10:05 lad Exp $
#
# balloon.tcl - procedures used by balloon help
#
# Copyright (C) 1996-1997 Stewart Allen
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 2
# of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

##############################################################################
#

bind Balloon(balloon) <Enter> {
 set Balloon(balloon,set) 0
 set Balloon(balloon,first) 1
 set Balloon(balloon,id) [after 500 {balloon %W $Balloon(balloon,%W)}]
}

bind Balloon(balloon) <Button> {
  set Balloon(balloon,first) 0
  kill_balloon
}

bind Balloon(balloon) <Leave> {
  set Balloon(balloon,first) 0
  kill_balloon
}

bind Balloon(balloon) <Motion> {
  if {$Balloon(balloon,set) == 0} {
    after cancel $Balloon(balloon,id)
    set Balloon(balloon,id) [after 500 {balloon %W $Balloon(balloon,%W)}]
  }
}

proc help_set_balloon {target message} {
global Balloon
  set Balloon(balloon,$target) $message
  bindtags $target "[bindtags $target] Balloon(balloon)"
}

proc kill_balloon {} {
global Balloon
  after cancel $Balloon(balloon,id)
  if {[winfo exists .balloon] == 1} {
    destroy .balloon
  }
  set Balloon(balloon,set) 0
}

proc balloon {target message} {
global Balloon xb
  if {$Balloon(balloon,first) == 1 && $Balloon(pr,balloon) == 1} {
    set Balloon(balloon,first) 2
    set x [expr [winfo rootx $target] + ([winfo width $target]/2)]
    set y [expr [winfo rooty $target] + [winfo height $target] + 4]
    toplevel .balloon -bg black
    wm overrideredirect .balloon 1
    label .balloon.l \
      -text $message -font $xb(font) -relief flat \
      -bg #ffffaa -fg black -padx 2 -pady 0 -anchor w
    pack .balloon.l -side left -padx 1 -pady 1
    wm geometry .balloon +${x}+${y}
    set Balloon(balloon,set) 1
  }
}

# #######################
# XBARNACLE SPECIFIC HELP
# #######################

# proc help_proof_tree_help
#
# Help information relating to the display of the proof tree.

proc help_proof_tree_help {} {
global xb node
  destroy .nodehelp
  toplevel .nodehelp 
  wm title .nodehelp "Help - Proof Trees"
  wm geometry .nodehelp +350+350
  frame .nodehelp.butt -bg $xb(bg)
  pack .nodehelp.butt -side bottom -fill x
  button .nodehelp.butt.done -text "Close" -command \
    "destroy .nodehelp" -bg $xb(bg) -fg $xb(fg) -font $xb(font)
  pack .nodehelp.butt.done -side bottom
  frame .nodehelp.fr1 -bg $xb(bg) -relief raised -bd 1
  pack .nodehelp.fr1 -side left -fill both -expand 1
  label .nodehelp.fr1.title -font $xb(font) -fg $xb(fg) -bg $xb(bg) \
    -text "Plan nodes"
  pack .nodehelp.fr1.title -side top -fill x
  canvas .nodehelp.fr1.canvas -bg white
  pack .nodehelp.fr1.canvas -side left -expand 1 -fill both
  set c .nodehelp.fr1.canvas
  $c create rectangle 60 60 280 115 -fill \
    $node(partial_status,colour) -outline black -width 3
  set text [text $c.text -height 1 -width 28 -relief sunken -font \
    $xb(font) -bg white -fg $xb(fg)]
  $c.text insert end "                  Goal"
  $c create window 65 65  -window $text -anchor nw
  $c create text 65 95 -text "Applied Method (where applicable)" \
    -font $xb(font) -fill black -anchor nw
  $c create text 60 46 -text "010" -font $xb(font) -anchor nw
  $c create text 3 10  -text "Address of node in proof" -font \
    $xb(font) -anchor nw
  $c create line 70 22 70 46 -arrow last -width 2
  $c create text 3 160 -text "Current node is denoted" -font \
    $xb(font) -anchor nw
  $c create text 3 174 -text "by heavy black border" -font $xb(font) \
    -anchor nw
  $c create line 70 158 90 118 -arrow last -width 2
  $c create text 160 167 -text "Colour denotes status of node" -font \
    $xb(font) -anchor nw
  $c create line 200 165 160 111 -arrow last -width 2
  $c configure -width 400 -height 250
  wm protocol .nodehelp WM_DELETE_WINDOW {set z 0}
}

# proc help_node_address_help
#
# Help information relating to node addresses displayed on the proof tree
# Called from the Help menu

proc help_node_address_help {} {
global xb node env
  destroy .nodeaddrhelp
  toplevel .nodeaddrhelp 
  wm title .nodeaddrhelp "Help - Node Addresses"
  wm geometry .nodeaddrhelp +350+350
  frame .nodeaddrhelp.butt -bg $xb(bg)
  pack .nodeaddrhelp.butt -side bottom -fill x
  button .nodeaddrhelp.butt.done -text "Close" \
    -command "destroy .nodeaddrhelp" -bg $xb(bg) -fg $xb(fg) \
    -font $xb(font)
  pack .nodeaddrhelp.butt.done -side bottom
  frame .nodeaddrhelp.fr1 -bg $xb(bg) -relief raised -bd 1
  pack .nodeaddrhelp.fr1 -side left -fill both -expand 1
  label .nodeaddrhelp.fr1.title -font $xb(font) -fg $xb(fg) -bg \
    $xb(bg) -text "Node Addresses"
  pack .nodeaddrhelp.fr1.title -side top -fill x
  text .nodeaddrhelp.fr1.explan -font $xb(font) -fg $xb(fg) -bg \
    $xb(bg) -relief flat -wrap word -bd 0 -height 9 -highlightthickness 0
  .nodeaddrhelp.fr1.explan insert end "Node addresses in XBarnacle are \
    calculated via the path from the root to the node.\n\nThe root is \
    given address 0 and for each child on the path to the node we add \
    (n-1) to the address where the child is the nth sub-goal of its \
    parent. So for the third child of a\n parent node we would add a \
    2.\n\nThe Node Addresses on Tree option in the Options menu \
    toggles the display of node addresses on the proof tree" 
  pack .nodeaddrhelp.fr1.explan -side bottom -fill x
  .nodeaddrhelp.fr1.explan configure -state disabled
  canvas .nodeaddrhelp.fr1.canvas -bg white -highlightthickness 0
  pack .nodeaddrhelp.fr1.canvas -side left -expand 1 -fill both
  image create photo tree -file \
    $env(LCLAM_GUI_DIR)/bitmaps/helptree.gif
  set c .nodeaddrhelp.fr1.canvas
  $c create image 70 10 -image tree -anchor nw
  $c create text 40 25 -text "The root node has address 0" -font \
    $xb(font) -anchor w 
  $c create text 20 90 -text "The first child of the" -font $xb(font) \
    -anchor w 
  $c create text 20 105 -text "root has address 00" -font $xb(font) \
    -anchor w 
  $c create text 250 60 -text "The nth child of the root has address \
    0(n-1)" -font $xb(font) -anchor w 
  $c create text 250 75 -text "In this case, the 3rd child has address \
    02" -font $xb(font) -anchor w 
  $c create text 250 105 -text "Being the first child of the above \
    node" -font $xb(font) -anchor w 
  $c create text 250 120 -text "we add a 0 to the address yielding \
    020" -font $xb(font) -anchor w 
  $c create text 250 150 -text "Being the first child of the above \
    node" -font $xb(font) -anchor w 
  $c create text 260 165 -text "we add a 0 to the address yielding \
    0200" -font $xb(font) -anchor w 
  $c configure -width 530 -height 250
  wm protocol .nodeaddrhelp WM_DELETE_WINDOW {set z 0}
}
