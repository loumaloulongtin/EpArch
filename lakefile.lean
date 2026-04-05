import Lake
open Lake DSL

package «EpArch» where
  -- add package configuration options here

lean_lib «EpArch» where
  -- add library configuration options here

@[default_target]
lean_exe «eparch» where
  root := `Main
