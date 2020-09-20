{-# LANGUAGE RecordDotSyntax #-}

no Foo { bar.baz = x } = undefined
  -- Syntax error: "Field selector syntax is not supported in
  -- patterns."
