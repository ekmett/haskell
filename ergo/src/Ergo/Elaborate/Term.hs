-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Ergo.Elaborate.Term where

import Ergo.Names
import Ergo.Icit

type Ty = Tm
type Ix = Int

data Tm a
  = Var !Ix                            -- ^ x
  | Let !Name !(Ty a) !(Tm a) !(Tm a)  -- ^ let x : A = t in u
  | Pi !Name !Icit !(Ty a) !(Ty a)     -- ^ (x : A) → B)  or  {x : A} → B
  | Lam !Name !Icit !(Ty a) !(Tm a)    -- ^ λ(x : A).t  or  λ{x : A}.t
  | App !Icit (Tm a) !(Tm a)           -- ^ t u  or  t {u}

  | Tel                                -- ^ Tel
  | TNil                               -- ^ ε
  | TCons !Name !(Ty a) !(Ty a)        -- ^ (x : A) ▷ B
  | Rec !(Tm a)                        -- ^ Rec A
  | Tnil                               -- ^ []
  | Tcons !(Tm a) !(Tm a)              -- ^ t :: u
  | Proj1 !(Tm a)                      -- ^ π₁ t
  | Proj2 !(Tm a)                      -- ^ π₂ t
  | PiTel !Name !(Ty a) !(Ty a)        -- ^ {x : A⃗} → B
  | AppTel !(Ty a) !(Tm a) !(Tm a)     -- ^ t {u : A⃗}
  | LamTel !Name !(Ty a) !(Tm a)       -- ^ λ{x : A⃗}.t

  | U                                  -- ^ U
  | Meta a                             -- ^ α
  | Skip !(Tm a)                       -- ^ explicit weakening for closing types
