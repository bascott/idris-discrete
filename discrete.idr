module Discrete

%access public export
%default total

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

isLTorEq : LTE a b -> Either (a = b) (LT a b)
isLTorEq LTEZero {a = Z} {b = Z} = Left Refl
isLTorEq LTEZero {a = Z} {b = (S _)} = Right (LTESucc LTEZero)
isLTorEq (LTESucc p) {a = (S _)} {b = (S _)}
  = case isLTorEq p of
         Left l => Left (cong l)
         Right r => Right (LTESucc r)

isGTorEq : GTE a b -> Either (a = b) (GT a b)
isGTorEq p = case isLTorEq p of
                  Left l => Left (sym l)
                  Right r => Right r

fromEqLTE : a = b -> a `LTE` b
fromEqLTE {a = Z} {b = Z} Refl = LTEZero
fromEqLTE {a = (S k)} {b = (S k)} Refl = LTESucc (fromEqLTE Refl)

ltePlusRight : (a + b) `LTE` c -> a `LTE` c
ltePlusRight {a = Z} {b = b} {c = c} x = LTEZero
ltePlusRight {a = (S k)} {b = b} {c = (S j)} (LTESucc x)
  = LTESucc $ ltePlusRight x

oneTimesOneOne : (m : Nat) -> (n : Nat) -> m * n = 1 -> (m = 1, n = 1)
oneTimesOneOne Z  _ Refl impossible
oneTimesOneOne m Z prf = let h = multCommutative m 0
                             h' = trans (sym h) prf in
                             (absurd h', h')
oneTimesOneOne (S Z) (S Z) prf = (Refl, Refl)
oneTimesOneOne (S Z) (S (S k)) prf
  = let h = succInjective (1 + k + 0) 0 prf in
        (Refl, absurd $ sym h)
oneTimesOneOne (S (S k)) (S Z) prf
  = let h = succInjective (1 + k * 1) 0 prf in
        (absurd $ sym h, Refl)
oneTimesOneOne (S (S k)) (S (S j)) prf
  = let h = succInjective (1 + j + (1 + k) * (2 + j)) 0 prf in
        (absurd $ sym h, absurd $ sym h)

multNeutralIsNeutral : (a : Nat) ->
                       (b : Nat) ->
                       {auto bNotZ : b = S _} ->
                       a * b = b ->
                       a = 1
multNeutralIsNeutral  Z  (S _) {bNotZ = Refl} Refl impossible
multNeutralIsNeutral (S Z) (S _) {bNotZ = Refl} prf = Refl
multNeutralIsNeutral (S (S k))  (S j) {bNotZ = Refl} prf
  = let h = succInjective (j + (1 + k) * (1 + j)) j prf in
        void $ plusRightNotZeroNotNeutral h
  where
    plusRightNotZeroNotNeutral : a + (S b) = a -> Void
    plusRightNotZeroNotNeutral Refl impossible

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

-------------------------------------------------------------------------------
-- Division
-------------------------------------------------------------------------------

data Divides : Nat -> Nat -> Type where
  P : (k : Nat ** k * m = n) -> m `Divides` n

divsSym : n `Divides` n
divsSym {n} = P (1 ** plusZeroRightNeutral n)

divsZero : m `Divides` Z
divsZero = P (Z ** Refl) 

divsLTE : m `Divides` n -> m `LTE` n

divsTrans : a `Divides` b -> b `Divides` c -> a `Divides` c
divsTrans {a} {c} (P (k ** pf)) (P (k' ** pf'))
  = let h = cong {f = mult k'} pf
        h' = trans (sym (multAssociative k' k a)) h in
        P (k' * k ** trans h' pf')

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
