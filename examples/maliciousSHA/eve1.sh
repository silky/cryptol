#�4@	�M��T�+��[Gx&��7+��P,uKW8�إ�D�Q*�6��⊟2U���z�

if [ `od -t x1 -j3 -N1 -An "${0}"` -eq "91" ]; then 
  echo "Cryptol";
else
  echo "Galois";
fi
