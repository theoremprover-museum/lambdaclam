# This file extracts out the 3 procedures that 
# were defined in the main xbarnacle file.
# They are re-ordered in the order they are called.
# 
# connected is called at the time the socket connection
# is established
#
# read_a_command is called at the bottom of xbarnacle
# and the first command it receives from lambda-prolog
# is 
#
# xbarnacle


# proc connected
#
# This procedure is executed when Tcl/Tk recieves a connection from
# LambdaCLaM. args is a list of information relating to the connection,
# the identity of the channel is the first element of this list.

proc connected {args} {
global Waited Commport
  puts "LambdaCLaM has connected to XBarnacle : $args"
  set Commport [lindex $args 0]
  puts "Communicating on channel $Commport"
  set Waited 1
}


# proc read_a_command
#
# Read a command until the marker XB_END is encountered. This allows
# commands from LambdaCLaM to have new-lines within them. XB_END should
# be sent from LambdaCLaM on a line by itself.

proc read_a_command {Commport} {
  set retrieved 0
  set complete_cmd ""
  while {!$retrieved} {
    gets $Commport cmd
    if {[regexp XB_END $cmd]} {
      set retrieved 1
      set cmd $complete_cmd
    } else {
      set complete_cmd "$complete_cmd$cmd"
    }
  }
  return $cmd
}

# proc xbarnacle
#
# Now does nothing....except print messages
#
# This procedure is called from LambdaCLaM and will load and initiate
# XBarnacle.
#
# env is a Tcl/Tk built-in global variable array that can be used to
# access the names of environment variables.

proc xbarnacle {} {
  #global env
  puts "Tcl/Tk: Starting up XBarnacle"
  # source $env(LCLAM_GUI_DIR)/src/START_UP.tcl
  puts stdout "X-Barnacle is ready."
}
