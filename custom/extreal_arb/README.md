# Customized HOL-Probability with old definitions of extreal_add/sub

## Changed definitions

```
Definition extreal_add_def :
   (extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add NegInf b = NegInf) /\
   (extreal_add c NegInf = NegInf) /\
   (extreal_add PosInf a = PosInf) /\
   (extreal_add a PosInf = PosInf)
End

Definition extreal_sub_def :
   (extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub NegInf c = NegInf) /\
   (extreal_sub b PosInf = NegInf) /\
   (extreal_sub c NegInf = PosInf) /\
   (extreal_sub PosInf a = PosInf)
End
```

## Added theorems

