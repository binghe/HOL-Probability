# Customized HOL-Probability with special definitions of extreals

## Changed definitions

The old definitions of `extreal_add` and `extreal_sub` in HOL4 (<= K12) wrongly allows
`PosInf + NegInf = PosInf`, `PosInf - PosInf = PosInf` and  `NegInf - NegInf = PosInf`:

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

## Added theorems (in newly added `fubiniTheory`)

* `add_comm`
* `add_assoc` (not used)
* `extreal_sub_add`
* `lt_sub`
* `lt_sub_imp`
* `IN_MEASURABLE_BOREL_ADD`
* `IN_MEASURABLE_BOREL_SUB`
* `integral_add_lemma`
* `FUBINI`
