#!/bin/bash

################################################################################################
# This script verifies all *.rs files inside a directory using verus.
#
# To run this script, make sure verus is installed and available in the command line
# To install verus, follow this: [https://github.com/verus-lang/verus/blob/main/INSTALL.md]
#
# To chech verus installation: >> verus --version
#
# To run this script: >> chmod +x verify_all.sh
#                     >> ./verify_all.sh
###############################################################################################


SEARCH_DIR="${1:-.}"

find "$SEARCH_DIR" -type f -name "*.rs" | while read -r rs_file; do
  echo "[Start] verifing: $rs_file..."
  
  # verify with Verus with --multiple-errors
  verus "$rs_file" --multiple-errors 20
  
  if [ $? -eq 0 ]; then
    echo "[Verified]: $rs_file"
    echo
  else
    echo "[Not Verified]: $rs_file"
    echo
  fi
done
