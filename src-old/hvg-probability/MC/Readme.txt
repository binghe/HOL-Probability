(******************************************************************)
(*                  MARKOV CHAIN FORMALIZATION IN HOL4            *)
(*                                                                *)
(*                      Copyright 2013, Liya Liu                  *)
(*                                                                *)
(*                      Contact: liy_liu@encs.concordia.ca        *)
(*                                                                *)
(******************************************************************)



INSTALLATION:

Requirement: HOL4 "Kanaskis" 7

1) open a terminal in the directory where you extracted the archive

2) run Holmake
  (this will build the corresponding *Theory.sig, *Theory.ui and
  *Theory.uo files)


OPTIONALLY:

- if you want to test the DNA application, open a HOL4
  session and type in:

  > use "dnaAppScript.sml";

  (the last theorem is the state path probability for the DNA
  sequence mentioned in the paper)

- to make use of the automation tactics, type in:

  > use "autohmmScript.sml";

  (the last three lines command give an example on how to calculate
  the joint probability and show the results)


CONTENTS OF THIS ARCHIVE:

  - Conditional probability theorems:
    * cond_probScript.sml 
    * setUsefulScript.sml

  - Discrete-time Markov chain theorems:
    * dtmcBasicScript.sml
    
  - Hidden Markov Model theorems:
    * hmmScript.sml

  - HMM Automation (collaboration with Dr. Vincent Aravantinos):
    * autohmmScript.sml
    
  - Formal analysis of a DNA sequences:
    * dnaAppScript.sml

  - Readme.txt: this file

  - Supporting theories of measure and probability, developped by
    Drs. Tarek Mhamdi and Joe Hurd (this is included in the archive
    for convenience):
    * subtypeScript.sml
    * rationalScript.sml
    * probabilityScript.sml
    * measureScript.sml
    * lebesgueScript.sml
    * formalizeUseful.sml
    * extrealScript.sml
    * extra_realScript.sml
    * extra_pred_setScript.sml
    * extra_numScript.sml
    * extra_listScript.sml
    * extra_boolScript.sml

