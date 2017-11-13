module NumIdris.Linear

%access public export

interface Linear a where
  (+) : a  -> a -> a
  -- zero
  zerol : a -> a
  inv : a -> a
