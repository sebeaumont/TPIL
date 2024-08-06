import Lake
open Lake DSL

package «tpil» where
  -- add package configuration options here

lean_lib «Tpil» where
  -- add library configuration options here

@[default_target]
lean_exe «tpil» where
  root := `Main
