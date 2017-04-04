module otter.

accumulate objlists.
accumulate constructive_logic.

top_goal otter otter_goal []
	(app forall (tuple [bool, (abs x\ (app and (tuple [x, (app neg x)])))])).

atomic otter otter_meth
	G
	(mathweb_get_service "OTTER" OtterService, 
        output std_out "service: ",
        output std_out OtterService,
        output std_out "\n",
        flush std_out,
%        Method is "prove(\"set(auto).\n formula_list(usable).\n all a (a * id = a).\n -(all a (a * id = a)).\n end_of_list.\" syntax: tptp replyWith: atp_result(state: unit output: unit host: unit name: unit))",
        Problem is "\"set(auto).\n formula_list(usable).\n all a (a * id = a).\n -(all a (a * id = a)).\n end_of_list.\"",
        mathweb_apply OtterService "prove" [["1", Problem], ["syntax", "tptp"]] 100 Result,
        printterm std_out Result,
        print "\n",
        flush std_out,
        mathweb_leave_service OtterService,
        print "service OTTER left\n",
        flush std_out, !)
	true
	trueGoal
	notacticyet.

end
