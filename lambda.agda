open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])

Id : Set
Id = String

infix 5  ƛ_⇒_
infix 5  μ_⇒_
infixl 7 _·_
infix 9 `_
infix 9 _[_:=_]

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc                 : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

plus : Term
plus = μ "+" ⇒ (ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ])

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no _ = ƛ x ⇒ N [ y := V ]
(M · N) [ y := V ] = M [ y := V ] · N [ y := V ]
`zero [ y := V ] = `zero
`suc N [ y := V ] = `suc (N [ y := V ])
case M [zero⇒ N₁ |suc x ⇒ N₂ ] [ y := V ] with x ≟ y
... | yes _ = case M [ y := V ] [zero⇒ N₁ [ y := V ] |suc x ⇒ N₂ ]
... | no _ = case M [ y := V ] [zero⇒ N₁ [ y := V ] |suc x ⇒ N₂ [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no _ = μ x ⇒ N [ y := V ]
