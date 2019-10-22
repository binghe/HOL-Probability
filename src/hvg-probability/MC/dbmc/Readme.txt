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

- if you want to test the Birth-Death process, open a HOL4
  session and type in:

  > use "dbScript.sml";

  (If an exception error appears, the most probable problem is the patch of HOL has not be installed properly
   so that the SML stack is not sufficent for scripts with many theorems. In this case, you should install the 
   patch for HOL4.)

CONTENTS OF THIS ARCHIVE:

  - Conditional Probability theorems:
    * cond_probScript.sml 
    * setUsefulScript.sml

  - Discrete-time Markov Chain theorems:
    * dtmcBasicScript.sml
    
  - Classified Discrete-time Markov Chain theorems:
    * classified_dtmcScript.sml

  - Extra Integer theorems:
    * integerSumScript.sml
  
  - Great Common Divisor of a Set theorems:
    * gcd_ofsetScript.sml
	
  - Birth-Death Process theorems:
    * dbScript.sml

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

