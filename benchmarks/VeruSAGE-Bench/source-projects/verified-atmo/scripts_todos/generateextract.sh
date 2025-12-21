#!/bin/bash

# Input file containing list of filenames
filelist="file_list.txt"

# Loop through each line in the input file
while IFS= read -r filename; do

  prefix="${filename%-poly.vir}"

  instr=$(echo "${prefix}" | sed 's/\&\%/\\\&\\\%/g')
  input_file="${instr}-poly.vir"

  # Add suffix for output file
  newstr=$(echo "${prefix}" | sed 's/&%//g')
  output_file="${newstr}.rs"

  # Generate the command
  echo "echo \"$filename\""
  echo "python3 ~/programs/Verus_Copilot/code/utils_rustmerger.py --inputdir ../. --input ../.verus-log/$input_file --outputAll $output_file"
  echo "sleep 1"
  echo " "
done < "$filelist"
