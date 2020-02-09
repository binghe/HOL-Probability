(* ========================================================================= *)
(* The Law(s) of Large Numbers (Probability Theory)                          *)
(*                                                                           *)
(* Author: Chun Tian (2020)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pred_setTheory realTheory realLib transcTheory
     real_sigmaTheory;

open real_topologyTheory derivativeTheory integrationTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory borelTheory
     real_borelTheory measureTheory lebesgueTheory probabilityTheory;

val _ = new_theory "large_num";

(* convergence modes: a.e. and pr. *)
val _ = Datatype `convergence_mode = almost_everywhere ('a p_space)
                                   | in_probability    ('a p_space)`;

val _ = overload_on ("a.e.", ``almost_everywhere``);
val _ = overload_on ("pr.",  ``in_probability``);

(* probability measures are in [0,1], reducing to normal reals loses nothing *)
val _ = overload_on ("Prob", ``\p s. real (prob p s)``);

(* convergence of real-valued random series (e.g. random_variable X p borel) *)
Definition converge_def :
  (* X converges to Y (a.e.) *)
  (converge (X :num->'a->real) (Y :'a->real) (almost_everywhere p) =
     AE x::p. ((\n. X n x) --> (Y x)) sequentially) /\
  (* X converges to Y (in pr.) *)
  (converge (X :num -> 'a -> real) Y (in_probability p) =
     !e. 0 < e ==>
         ((\n. Prob p {x | x IN p_space p /\ e < abs (X n x - Y x)}) --> 0) sequentially)
End

(* convergence of extreal-valued random series [1, p.68,70] *)
Definition ext_converge_def :
  (* X converges to Y (a.e.) *)
  (ext_converge (X :num->'a->extreal) (Y :'a->extreal) (almost_everywhere p) <=>
     AE x::p. Y x <> PosInf /\ Y x <> NegInf /\
              ((\n. real (X n x)) --> real (Y x)) sequentially) /\
  (* X converges to Y (in pr.) *)
  (ext_converge (X :num->'a->extreal) (Y :'a->extreal) (in_probability p) =
    !e. 0 < e /\ e <> PosInf ==>
        ((\n. Prob p {x | x IN p_space p /\ e < abs (X n x - Y x) /\
                              ((X n x <> PosInf /\ Y x <> PosInf) \/
                               (X n x <> NegInf /\ Y x <> NegInf))}) --> 0) sequentially)
End

val _ = overload_on ("-->", ``converge``);
val _ = overload_on ("-->", ``ext_converge``);

(* Theorem 4.1.1 [1, p.69] (2) *)
Theorem ext_converge_AE_thm :
    !p X Y. prob_space p /\ (!n. random_variable (X n) p Borel) /\
            random_variable Y p Borel ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            ((\m. Prob p {x | x IN p_space p /\
                             !n. m <= n ==> abs (X n x - Y x) <= e /\
                                (X n x <> PosInf /\ Y x <> PosInf \/
                                 X n x <> NegInf /\ Y x <> NegInf)}) --> 1) sequentially)
Proof
    cheat
QED

(* Theorem 4.1.1 [1, p.69] (2') *)
Theorem ext_converge_AE_thm' :
    !p X Y. prob_space p /\ (!n. random_variable (X n) p Borel) /\
            random_variable Y p Borel ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            ((\m. Prob p {x | x IN p_space p /\
                             ?n. m <= n ==> e < abs (X n x - Y x) /\
                                (X n x <> PosInf /\ Y x <> PosInf \/
                                 X n x <> NegInf /\ Y x <> NegInf)}) --> 1) sequentially)
Proof
    cheat
QED

val _ = export_theory ();

(* References:

  [1] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
 *)
