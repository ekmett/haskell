-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Ergo.Elaborate.Term where

import Ergo.Elaborate.Value
import Ergo.Names
import Ergo.Icit

type Ty = Tm
type Ix = Int

data Tm s a
  = Var !Ix                            -- ^ x
  | Let !(Name s) !(Ty s a) !(Tm s a) !(Tm s a)  -- ^ let x : A = t in u
  | Pi !(Name s) !Icit !(Ty s a) !(Ty s a)     -- ^ (x : A) → B)  or  {x : A} → B
  | Lam !(Name s) !Icit !(Ty s a) !(Tm s a)    -- ^ λ(x : A).t  or  λ{x : A}.t
  | App !Icit (Tm s a) !(Tm s a)           -- ^ t u  or  t {u}

  | Tel                                -- ^ Tel
  | TNil                               -- ^ ε
  | TCons !(Name s) !(Ty s a) !(Ty s a)        -- ^ (x : A) ▷ B
  | Rec !(Tm s a)                        -- ^ Rec A
  | Tnil                               -- ^ []
  | Tcons !(Tm s a) !(Tm s a)              -- ^ t :: u
  | Proj1 !(Tm s a)                      -- ^ π₁ t
  | Proj2 !(Tm s a)                      -- ^ π₂ t
  | PiTel !(Name s) !(Ty s a) !(Ty s a)        -- ^ {x : A⃗} → B
  | AppTel !(Ty s a) !(Tm s a) !(Tm s a)     -- ^ t {u : A⃗}
  | LamTel !(Name s) !(Ty s a) !(Tm s a)       -- ^ λ{x : A⃗}.t

  | U                                  -- ^ U
  | Meta a                             -- ^ α
  | Skip !(Tm s a)                       -- ^ explicit weakening for closing types

type TM s = Tm s (Meta s)
type TY s = Ty s (Meta s)

