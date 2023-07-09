import Lake
open Lake DSL

package «fun» {
  -- add package configuration options here
}

lean_lib «Fun» {
  -- add library configuration options here
}

@[default_target]
lean_exe «fun» {
  root := `Main
}
