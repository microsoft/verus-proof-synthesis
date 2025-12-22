#!/bin/bash

while IFS= read -r file; do
  sed -i "1s|^|extern crate verus_builtin_macros as builtin_macros;\n|" "$file"
done < builtin_file.list
