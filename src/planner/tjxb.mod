% This module implements a socket based client which is (usually)
% called by a Tcl/Tk server (XBarnacle) for the purposes
% of running the lclam module under a graphical user interface.

% Gordon Reid - January 10 2001.
% Last modified. Feb 6 2001.


% Original comment  by Chuck Liang for the socket code
% This module demonstrates the "open_socket" built-in predictate.
% 1. Start the java application ("java tjgui" on systems with jdk).
% 2. When the java frame comes up, click on the "listen" button. 
% 3. Load tjclient module and query teyjus with ?- go "127.0.0.1".
% 4. Now initiate a two-way chat by sending a message from the java frame.
%    The messages must be in lock-step.

module tjxb.

accumulate ordl.

type xb string -> int -> o.
type interact string -> in_stream -> out_stream -> o.
type xb_go  o.
type xbmode in_stream ->  out_stream -> o.
type xb_tree  o.

% This doesn't on Linux if Server isn't a fully
% qualified name
% it also doesn't work at all on RH5.1 after the connect
% see laptop version of teyjus special C code htons added

xb Hostname Port:- 
  open_socket Hostname Port In Out,
 /* (xbmode In Out) => xb_go. */
  (xbmode In Out) => xb_tree.

/*   print "Connected.  Waiting for communication ...\n\n",
  input_line In G, 
  print "from gui: ", print G,
  interact G In Out.
  */

% Tcl/Tk sends \r\n even though the string in the code only says \n

interact "exit\r\n" In Out :- print "exiting", close_in In, close_out Out, !.

interact "cont\r\n" In Out:- print "sub clause\n",  interact "" In Out.

% String_to_term doesn't seem to work on the strings from Tcl yet.
%interact S In Out :- print "In string ", print S, 
%		      string_to_term S A, 
%		      print "did it\n", interact "" In Out.

interact S In Out :- 
  print "\nto gui: ", 
  input_line std_in Line,
  output Out Line,  flush Out,
  input_line In S2,
  print "\nfrom gui: ", 
  print S2,
  interact S2 In Out.


% Additional Note:
% The predicate "readterm" requires multiple flushes from the server side.

xb_go:- print "In XB_go\n", 
	xbmode In Out, 
	printterm std_out In,
	printterm std_out Out,
	input_line In S2,
	printterm std_out S2,
	interact "" In Out.

xb_tree:- xbmode In Out,
	  output Out "\nxbarnacle\nXB_END\n",
	(interactive xbarnacle => xbloop
		(set_sym_eval_list [plus1, plus2, idty],
        	(set_wave_rule_list [plus2],
		(set_induction_scheme_list [nat_struct],
		(plan_this pds_planner induction_top_meth 
						assp depth_first_plan))))).

xbloop xbend:-
	xbmode In Out,
	output Out "\nmisc_poll_user_event\nXB_END\n",
	interact "" In Out.
xbloop (H, T):-!,
	execute_command H (xbloop T).
xbloop H :- !,
	execute_command H (xbloop xbend).
