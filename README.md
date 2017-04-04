Installing lclam
----------------
The installation process requires the setting of several environment
variables.  We advise these are set in the .bashrc file (or .benv file 
on DReaM group machines) to avoid repetitious resetting everytime you
wish to use lclam.

1. Install Teyjus Prolog.   
NB.  For Macs may need to set the heapsize in config.h by hand
(suggest 262144).   

2. Set the enviroment variable TEYJUS_HOME to point to the directory
containing the tjsim executable.  (On the Dream machines this is
already set for you.)

3. Set your PATH to point to the directory containing the tjsim executable
(on Dream machines this is already set for you).

4. Download lclam.tar.gz from the Dream Group home page.  Uncompress it. 
You should get a top level directory lambda-clam-teyjus/.

5. Enter this directory and set the environment variable LCLAM_HOME to
point to it. 

6. Add: $LCLAM_HOME/src/compiler
$LCLAM_HOME/src/core_theories
$LCLAM_HOME/src/gs
$LCLAM_HOME/src/interface 
$LCLAM_HOME/src/io
$LCLAM_HOME/src/mathweb
$LCLAM_HOME/src/planner
$LCLAM_HOME/src/syntax
$LCLAM_HOME/src/theories
$LCLAM_HOME/src/theories/tutorial
$LCLAM_HOME/src/util
to TJPATH.
(At some point soon we hope to include a script in the distribution
to do this for you.  We apologise for the current inconvenience.)

7. Enter the directory $LCLAM_HOME/src/

8. Type make.
NB.  You may want to do this in emacs and then search the output
for error messages.

To Run lclam in the Shell 
------------------------- 
NB. We recommend you use the ProofGeneral interface for most
applications.  See below for details.

1.  Check TJPATH is set up as described above.

2.  Type $LCLAM_HOME/bin/lclam.  Alternatively put $LCLAM_HOME/bin on
your PATH and type lclam (WARNING: Typing lclam on the Dream machines
will get you an older version of lclam).

basic usage:
To exit lclam type quit.
To exit lclam and teyjus type halt.
To test lclam is working type testpds.  (This will generate a lot
of output, but each attempt is started with Checking and should end with
Plan Succeeded)

More details on commands can be found in the manual.


To Run lclam in ProofGeneral 
---------------------------- 
The ProofGeneral interface is included
in the CVS distribution.  To install it, add the following line to
your .emacs file:

(load "LCLAM_PATH/lambda-clam-teyjus/ProofGeneral/generic/proof-site.el")

where LCLAM_PATH is the path to your lambda-clam-teyjus directory.

Opening a file with the extension .lcm in XEmacs will now
automatically invoke ProofGeneral with lclam.  Proof planning commands
are given in the top buffer; step through them using the Next button
on the toolbar.  The lclam output is shown in the lower buffer.


To Get the Documentation
-----------------------

1. You will need latex and dvips.

2. From the directory lambda-clam-teyjus enter the directory doc.

3. Type make.  

4. The manual is in the file manual.ps.  There are release notes in 
the release_notes directory and some other miscellaneous documentation 
in the doc directory.


