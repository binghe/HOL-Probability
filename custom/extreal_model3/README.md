# Customized HOL-Probability with special definitions of extreals

## Changed definitions

```
Definition extreal_add_def :
   (extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add (Normal _) a = a) /\
   (extreal_add b (Normal _) = b) /\
   (extreal_add NegInf NegInf = NegInf) /\
   (extreal_add PosInf PosInf = PosInf) /\
   (extreal_add PosInf NegInf = Normal 0) /\
   (extreal_add NegInf PosInf = Normal 0)
End

Definition extreal_sub_def :
   (extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub a (Normal _) = a) /\
   (extreal_sub (Normal _) NegInf = PosInf) /\
   (extreal_sub (Normal _) PosInf = NegInf) /\
   (extreal_sub NegInf PosInf = NegInf) /\
   (extreal_sub PosInf NegInf = PosInf) /\
   (extreal_sub PosInf PosInf = Normal 0) /\
   (extreal_sub NegInf NegInf = Normal 0)
End
```

The above definitions are equivalent with those in Mizar (`xxreal_3`):

```
definition
  let x,y be ExtReal;
  func x + y -> ExtReal means
:: XXREAL_3:def 2

  ex a,b being Complex st x = a & y = b & it = a + b
  if x is real & y is real,
  it = +infty if x = +infty & y <> -infty or y = +infty & x <> -infty,
  it = -infty if x = -infty & y <> +infty or y = -infty & x <> +infty
  otherwise it = 0;
  commutativity;
end;
```

## Added theorems (in newly added `fubiniTheory`)

* `add_comm`
* `extreal_sub_add`
* `IN_MEASURABLE_BOREL_ADD`
* `IN_MEASURABLE_BOREL_SUB`
* `integral_add_lemma`
* `FUBINI`
