module Discrete

%default total

isLTorEq : LTE a b -> Either (a = b) (LT a b)
isLTorEq LTEZero {a = Z} {b = Z} = Left Refl
isLTorEq LTEZero {a = Z} {b = (S _)} = Right (LTESucc LTEZero)
isLTorEq (LTESucc p) {a = (S _)} {b = (S _)}
  = case isLTorEq p of
         Left l => Left (cong l)
         Right r => Right (LTESucc r)

isGTorEq : GTE b a -> Either (b = a) (GT b a)
isGTorEq p = case isLTorEq p of
                  Left l => Left (sym l)
                  Right r => Right r

inductionPrinciple : {p : Nat -> Type} ->
                     {nGTEa : GTE n a} ->
                     p a ->
                     ((k : Nat) -> GTE k a -> p k -> p (S k)) ->
                     p n
inductionPrinciple {n} {nGTEa} base step with (isGTorEq nGTEa)
  inductionPrinciple {n = a} base step | Left Refl = base
  inductionPrinciple {n = Z} base step | Right (LTESucc _) impossible
  inductionPrinciple {n = (S m)} base step | Right (LTESucc mGTEa) 
  = let ih = inductionPrinciple {p} {n = m} {nGTEa = mGTEa} base step in
        step m mGTEa ih

data Divides : Nat -> Nat -> Type where
  P : (k : Nat ** k * m = n) -> m `Divides` n

divsSym : n `Divides` n
divsSym {n} = let divsSymProof = plusZeroRightNeutral n in
                  P (1 ** divsSymProof)

divsZero : m `Divides` Z
divsZero = P (Z ** Refl) 

divsLTE : m `Divides` n -> m `LTE` n

divsTrans : a `Divides` b -> b `Divides` c -> a `Divides` c
divsTrans {a} {c} (P (k ** pf)) (P (k' ** pf'))
  = let h = sym (multAssociative k' k a)
        h' = trans (cong {f = mult k'} pf) pf' in
        P (k' * k ** trans h h')

divsAntiSym : a `Divides` b -> b `Divides` a -> a = b

divsCombination : a `Divides` b ->
                  a `Divides` c ->
                  a `Divides` (p * b + q * c)
divsCombination {p} {q} (P (k ** pf)) (P (k' ** pf'))
  = rewrite sym pf in
    rewrite sym pf' in
    rewrite multAssociative p k a in 
    rewrite multAssociative q k' a in 
    rewrite sym (multDistributesOverPlusLeft (p * k) (q * k') a) in
            P ((p * k) + (q * k') ** Refl)

divsMultiple : a `Divides` b -> a `Divides` (p * b)
divsMultiple {p} (P (k ** pf)) = rewrite sym pf in
                                 rewrite multAssociative p k a in
                                         P (p * k ** Refl)
