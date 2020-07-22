# Customized HOL-Probability with old definitions of extreal add/sub #

## Introduction

The old definitions of `extreal_add` and `extreal_sub` wrongly allows `PosInf + NegInf = PosInf`,
`PosInf - PosInf = PosInf` and  `NegInf - NegInf = PosInf`:

```
val extreal_add_def = Define
  `(extreal_add (Normal x) (Normal y) = (Normal (x + y))) /\
   (extreal_add PosInf a = PosInf) /\
   (extreal_add a PosInf = PosInf) /\
   (extreal_add NegInf b = NegInf) /\
   (extreal_add c NegInf = NegInf)`;

val extreal_sub_def = Define
  `(extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub PosInf a = PosInf) /\
   (extreal_sub b PosInf = NegInf) /\
   (extreal_sub NegInf NegInf = PosInf) /\
   (extreal_sub NegInf c = NegInf) /\
   (extreal_sub c NegInf = PosInf)`;
```

But it turns out that, with these definitions the commutativity and associativity of extreals are preserved, and this allows simplified antecedents of many lemmas, and makes the original version of Fubini's theorem provable.

## Changed Theorems

