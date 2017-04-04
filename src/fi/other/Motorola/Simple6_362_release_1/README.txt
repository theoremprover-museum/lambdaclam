README.txt

These are brief notes about the POTS Feature Interaction benchmark
SDL system.

* SDT System file is Network.sdt

* Once you start a simulation, there are several scripts available that
exercise and demonstrate specific behaviors of the system.  These are
divided into two groups:

	Feature Demonstration Scripts - these demonstrate the fundamental
	(Basic Call) and additional 10 features that have been implemented.
	There are 11 additional feature scripts, since Three way Calling
	(TC) is demonstrated twice, once with the originator initiating the
	TC feature, and once with the terminator initiating the feature.
	
	Sample Binary Interactions (Hall Results) - these walk the system
	through particular scenarios that illustrates two-way (hence
	"binary") feature interactions.  All of the 10 features eventually
	participate in at least one feature interaction.

Each script has a similar set of initial actions:

	> turns on MSC tracing
	> "provisions" each "user"
	> "sets up" each "user"

Then the system is driven with the actual "user" events associated with
the scenario being demonstrated.

* These are the 12 Feature Demonstration Scripts with associated brief
descriptions:

	BC - Basic Call
		1 goes off hook, 1 dials 4, 1 and 4 get connected, 4 goes off
		hook, 4 goes on hook, 1 goes on hook

	CFB - Call Forward on Busy
		1 has forward to 3 , 2 has a forward to 1, 1 dials 4, 1 and 4
		get connected, then 2 dials 1, 2 and 3 get connected
	
	CNDB - Calling Number Delivery Blocking
		User 1 has CNDB active (i.e. annonumus caller in every
		originating call, 1 dials 4, 1 and 4 get connected, ONE of the
		two goes onhook first

	CW - Call Waiting
		Call waiting all active, 1 dials 4, 1 and 4 get connected, then
		2 dials 1, 1 flashes, 1 switches to 2, 1 flashes, 1 switches to
		4 again  , 1 flashes, 1 switches to 2, ONE of the three goes
		onhook first

	RB - Ring Back when free
		RB on all, 1 dials 4, 1 and 4 get connected, then 2 dials 1,
		Gets the ring back message.

	RC - Reverse Charging
		User 1 Reverse Charging on user 4, 1 dials 4, 1 and 4 get
		connected, ONE of the two goes onhook first

	SB - Split Billing
		SB on 1 for 4, 1 dials 4, 1 and 4 get connected, ONE of the two
		goes onhook first

	TCS - Terminating Call Screening
		4 has a screen on 1, 1 dials 4, 1 get announced for screening,
		then 2 dials 4, gets connected

	TC_o - Three way Calling: originator initiated
		Three way all active,  All other features are disabled on all,
		1 dials 4, 1 and 4 get connected, 1 flashes, 1 dials 2, 1 and 2
		get connected, 1 flashes, 1,2 and 4 get connected, ONE of the
		three goes onhook first

	TC_t - Three way Calling: terminator initiated
		Three way all active,  All other features are disabled on all,
		1 dials 4, 1 and 4 get connected, 4 flashes, 4 dials 2, 4 and
		2 get connected, 4 flashes, 1,2 and 4 get connected, ONE of the
		three goes onhook first

	TL - Teen Line
		Off hook, announcing that pin is required, bad pin entered
		"16", on hook, second try good pin entered "17"

	VM - Voice Mail
		VM on all, 1 dials 4, 1 does not answer, 4 leaves a VM message,
		1 checks his messages

* These are the 6 Interaction Scripts with associated brief descriptions
(the descriptions are drawn from Hall's Feature Interaction Entry
paper):

	CFB_CFB_1
	  CFB/CFB(1) - B forwards to C, C forwards to D.  B calls C.
	  A calls B. D gets alerted, but A won't respond to the second
	  i_notify because A is in CFB-2.  Thus, A hangs forever.

	CW_TCS_1
	  CW/TCS(1) - B has TCS screening C.  B has CW.  A calls B.  During
	  that call, C calls B and gets through via CW.  C should have been
	  screened.

	TC_TL_1
	  TC/TL(1) - A has TL and TC.  During restrict time, if B calls A,
	  then A can flash and successfully make a call to anybody without
	  the PIN.

	TC_CNDB_1
	  TC/CNDB(1) - A has TC.  A has CNDB.  A calls B.  During that
	  call, A flashes and calls C.  C receives CID of A (not
	  anonymous).

	RC_SB_1
	  RC/SB(1) [TYPE I] - B has both RC and SB with the split amount
	  less than 100 (say 50).  A offhooks and dials B.  This results
	  in inconsistent output billing events:
	  billing_split(A, B, 50) vs billing_reverse(A, B, -).

	RB_VM_3
	  RB/VM(3) - A user in any persistent voice mail state (VM-3, VM-4,
	  VM-6) will fail to record incoming calls for later ringback.
	  This is illustrated in one scenario.
