{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, MagicHash, UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_HADDOCK not-home #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Conc.IOCP
-- Copyright   :  (c) The University of Glasgow, 1994-2002
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC extensions)
--
-- Windows I/O Completion Port interface to the one defined in
-- GHC.Event.Windows.
--
-- This module is an indirection to keep things in the same structure as before
-- but also to keep the new code where the actual I/O manager is.  As such it
-- just re-exports GHC.Event.Windows.Thread
--
-----------------------------------------------------------------------------

-- #not-home
module GHC.Conc.IOCP
       ( module GHC.Event.Windows.Thread ) where

import GHC.Event.Windows.Thread