import Lake
open Lake DSL

package corten {
  -- add package configuration options here
}

lean_lib Corten {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe corten {
  root := `Main
}
