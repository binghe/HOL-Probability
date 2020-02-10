(* ========================================================================= *)
(* The Law(s) of Large Numbers (Probability Theory)                          *)
(*                                                                           *)
(* Author: Chun Tian (2020)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pred_setTheory realTheory realLib transcTheory
     real_sigmaTheory real_topologyTheory derivativeTheory integrationTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory borelTheory
     real_borelTheory measureTheory lebesgueTheory probabilityTheory;

val _ = new_theory "large_num";

(* L^p integrable *)
Definition L_integrable_def :
  (L_integrable (Normal r) m f <=> 0 < r /\
     f IN measurable (m_space m,measurable_sets m) Borel /\
     pos_fn_integral m (\x. (abs (f x)) powr (Normal r)) <> PosInf) /\

  (L_integrable PosInf m f <=>
     f IN measurable (m_space m,measurable_sets m) Borel /\
     ?c. 0 < c ==> (measure m {x | c <= abs (f x)} = 0))
End

val _ = overload_on ("integrable", ``L_integrable``);

(* convergence modes: a.e. and pr. *)
val _ = Datatype `convergence_mode = almost_everywhere ('a p_space)
                                   | in_probability    ('a p_space)
                                   | in_distribution   ('a p_space)
                         (* L^p *) | in_space  extreal ('a p_space)`;

(* abbreviations of convergence modes (disabled)
val _ = overload_on ("a.e.",    ``almost_everywhere``);
val _ = overload_on ("in_pr.",  ``in_probability``);
val _ = overload_on ("in_dist", ``in_distribution``);
 *)

(* probability measures are in [0,1], reducing to normal reals loses nothing *)
val _ = overload_on ("Pr", ``\E p. real (prob p E)``);
val _ = overload_on ("Ex", ``\E p. real (expectation p E)``);

(* MATHEMATICAL SCRIPT CAPITAL P (disabled)
val _ = Unicode.unicode_version {u = UTF8.chr 0x1D4AB, tmnm = "Pr"};
 *)

(* convergence of real-valued random series (not used)
Definition converge_def :
  (* X converges to Y (a.e.) *)
  (converge (X :num->'a->real) (Y :'a->real) (almost_everywhere p) =
     AE x::p. ((\n. X n x) --> (Y x)) sequentially) /\
  (* X converges to Y (in pr.) *)
  (converge (X :num -> 'a -> real) Y (in_probability p) =
     !e. 0 < e ==>
         ((\n. Pr {x | x IN p_space p /\ e < abs (X n x - Y x)} p) --> 0) sequentially)
End

val _ = overload_on ("-->", ``converge``); (* from utilProbTheory *)
 *)

(* convergence of extreal-valued random series [1, p.68,70] *)
Definition ext_converge_def :
  (* X(n) converges to Y (a.e.) *)
  (ext_converge (X :num->'a->extreal) (Y :'a->extreal) (almost_everywhere p) <=>
       AE x::p. Y x <> PosInf /\ Y x <> NegInf /\
                ((\n. real (X n x)) --> real (Y x)) sequentially) /\

  (* X(n) converges to Y (in pr.) *)
  (ext_converge (X :num->'a->extreal) (Y :'a->extreal) (in_probability p) <=>
       !e. 0 < e /\ e <> PosInf ==>
           ((\n. Pr {x | x IN p_space p /\ e < abs (X n x - Y x) /\
                          ((X n x <> PosInf /\ Y x <> PosInf) \/
                           (X n x <> NegInf /\ Y x <> NegInf))} p) --> 0) sequentially) /\

  (* X(n) converges to Y (in L^p) *)
  (ext_converge (X :num->'a->extreal) (Y :'a->extreal) (in_space r p) <=>
       0 < r /\ r <> PosInf /\ (!n. integrable r p (X n)) /\ integrable r p Y /\
       (((\n. Ex (\x. (abs (X n x - Y x)) powr r) p) --> 0) sequentially))
End

val _ = overload_on ("-->", ``ext_converge``); (* from utilProbTheory *)

(* separate convergence definitions *)
val [ext_convergence_AE,
     ext_convergence_PR,
     ext_convergence_LP] =
    map save_thm (combine (["ext_convergence_AE",
                            "ext_convergence_PR",
                            "ext_convergence_LP"], CONJUNCTS ext_converge_def));

(* Theorem 4.1.1 [1, p.69] (2) *)
Theorem ext_converge_AE_iff :
    !p X Y. prob_space p /\ (!n. random_variable (X n) p Borel) /\
            random_variable Y p Borel ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
           ((\m. Pr {x | x IN p_space p /\
                        !n. m <= n ==> abs (X n x - Y x) <= e /\
                          ((X n x <> PosInf /\ Y x <> PosInf) \/
                           (X n x <> NegInf /\ Y x <> NegInf))} p) --> 1) sequentially)
Proof
    cheat
QED

(* Theorem 4.1.1 [1, p.69] (2') *)
Theorem ext_converge_AE_iff' :
    !p X Y. prob_space p /\ (!n. random_variable (X n) p Borel) /\
            random_variable Y p Borel ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
           ((\m. Pr {x | x IN p_space p /\
                        ?n. m <= n ==> e < abs (X n x - Y x) /\
                          ((X n x <> PosInf /\ Y x <> PosInf) \/
                           (X n x <> NegInf /\ Y x <> NegInf))} p) --> 0) sequentially)
Proof
    cheat
QED

(* Theorem 4.1.2 [1, p.70]: convergence a.e. implies convergence in pr. *)
Theorem ext_converge_AE_PR :
    !p X Y. prob_space p /\ (!n. random_variable (X n) p Borel) /\
            random_variable Y p Borel /\
           (X --> Y) (almost_everywhere p) ==> (X --> Y) (in_probability p)
Proof
    cheat
QED

val _ = export_theory ();

(* References:

  [1] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
 *)
