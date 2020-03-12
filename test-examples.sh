
for i in */examples/*
do
    cargo test --example $(basename $i .rs)
done
