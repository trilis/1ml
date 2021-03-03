for filename in examples/implicit_modules/*
do
  echo $filename;
  ./1ml $filename > /dev/null;
  if [[ 0 -eq $? ]]; then
    echo "OK"
  else 
    echo "FAIL"
  fi
done;