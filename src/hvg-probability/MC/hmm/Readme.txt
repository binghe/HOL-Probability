(******************************************************************)
(*                  Readme.txt (Editted by Liya Liu)              *)
(******************************************************************)
In this archived package, the following files are contained:
1) The measure and probability theorems developed by Dr. Tarek Mhamadi and Dr. Joe Hurd.
   subtypeScript.sml
   rationalScript.sml
   probabilityScript.sml
   measureScript.sml
   lebesgueScript.sml
   formalizeUseful.sml
   extrealScript.sml
   extra_realScript.sml
   extra_pred_setScript.sml
   extra_numScript.sml
   extra_listScript.sml
   extra_boolScript.sml
2) The conditional probability theorems and some useful theorems developed by Liya Liu.
   cond_probScript.sml 
   setUsefulScript.sml
3) The Discrete-time Markov chain theorems developed by Liya Liu.
    dtmcBasicScript.sml
4) The Hidden Markov Model theorems developed by Liya Liu.
    hmmScript.sml
5) The Automation code on HMMs developed by Dr. Vincent Aravantinos and Liya Liu
    autohmmScript.sml
6) The code for formal analysis of a DNA sequence application (by Liya Liu)
    dnaAppScript.sml

(*----------------------------------------------------------------*)
(*                  How to run the code properly ?                *)
(*----------------------------------------------------------------*)	
These code can be run in Kananaskis 7 correctly, so Kananaskis 7 should be installed first.
1) Download the archived file properly and compressed them to any path. 
2) Copy the files listed in 1), 2), 3), and 4) in previous section to a new folder.
3) Open a HOL4 session and compile the theorems in these files by using Holmake command.
   If you want to know how to use the parameters in Holmake command, you can type
   Holmake -- help
4) After all the theorems are compiled successfully, 
   the corresponding *Theory.sig, *Theory.ui and *Theory.uo will be created.
5) Now, you can copy the code in dnaAppScript.sml and paste it to HOL4 session to run all the theorems. 
   More simple, you can directly type the following line in HOL4 session:
   use "dnaAppScript.sml";
   The last theorem is to verify the state path probability for the DNA sequence mentioned in the paper.
6) If you want to enjoy the automated theorem proving code, then you can copy and paste the code in the 
   autohmmScript.sml file. The last three lines command give an example on how to calculate the joint 
   probability and show the results.
   
(*----------------------------------------------------------------*)
(*                  Now you can enjoy it !!!                      *)
(*----------------------------------------------------------------*)   
	