# The temperature is the first argument, which is default to 1.0
temp=${1:-1.0}
target=${2:-"MBPP"}
config_file=${3:-"config.json"}
model=${4:-"gpt4o"}

date=$(date '+%Y%m%d')

unverified_dir="../benchmarks/$target/unverified"
dir_name="_output/$date-$model-$target-$temp"

mkdir -p $dir_name

for i in {1..3}; do
    for filename in $(ls $unverified_dir); do
        if [ -f "$dir_name/$i-$filename" ]; then
            echo "Skipping $filename Step $i"
            continue
        fi
        echo "Running $filename Step $i"
        { time python main.py --temp $temp --mode gen --config $config_file --input $unverified_dir/$filename --output "$dir_name/$i-$filename"; } 2> "$dir_name/$i-$filename.time"
    done
done
