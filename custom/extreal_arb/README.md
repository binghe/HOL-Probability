# Customized HOL-Probability with old definitions of extreal_add/sub

## Changed definitions

```
Definition extreal_add_def :
   (extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add (Normal _) a = a) /\
   (extreal_add b (Normal _) = b) /\
   (extreal_add NegInf NegInf = NegInf) /\
   (extreal_add PosInf PosInf = PosInf) /\
   (extreal_add PosInf NegInf = ARB) (* here *) /\
   (extreal_add NegInf PosInf = ARB) (* here *)
End

Definition extreal_sub_def :
   (extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub a (Normal _) = a) /\
   (extreal_sub (Normal _) NegInf = PosInf) /\
   (extreal_sub (Normal _) PosInf = NegInf) /\
   (extreal_sub NegInf PosInf = NegInf) /\
   (extreal_sub PosInf NegInf = PosInf) /\
   (extreal_sub PosInf PosInf = ARB) (* here *) /\
   (extreal_sub NegInf NegInf = ARB) (* here *)
End
```

## Added theorems

