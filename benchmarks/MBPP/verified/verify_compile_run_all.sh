#!/bin/bash

################################################################################################
# This script verifies and compiles all *.rs files 
# inside a directory using verus and runs the test cases.
# It also removes all compiled files after test execution.
#
# To run this script, make sure verus and verusfmt are installed and available in the command line
# To install verus, follow this: [https://github.com/verus-lang/verus/blob/main/INSTALL.md]
# To install verusfmt follow this: [https://github.com/verus-lang/verusfmt]
#
# To chech verus installation, try: >> verus --version
#
# To run this script: >> chmod +x verify_compile_run_all.sh
#                     >> ./verify_compile_run_all.sh
###############################################################################################

SEARCH_DIR="${1:-.}"

find "$SEARCH_DIR" -type f -name "*.rs" | while read -r rs_file; do
  echo "[Start] verifing and compiling: $rs_file..."
  
  base_name=$(basename "$rs_file" .rs)
  
  # format the source first
  verusfmt "$rs_file"
  # verify and compile with Verus
  verus "$rs_file" --compile --multiple-errors 20

  if [ $? -eq 0 ]; then
    echo "[Verified] and [Compiled]: $rs_file"
    echo "[Run] Tests: $rs_file"
    ./$base_name
    if [ $? -eq 0 ]; then
      echo "[Passed] Tests: $rs_file"
    else
      echo "[Falied] Tests: $rs_file"
    fi

    if [ -e "$base_name" ]; then
      echo "[Removed] compiled file: $base_name"
      rm $base_name
    else
      echo "[Not Found] compiled file: $base_name"
    fi 
  else
    echo "[Not Verified]: $rs_file"
  fi
   echo
done
