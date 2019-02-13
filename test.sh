bash -c "cd /tmp/output_fsti; ls -1 | xargs -I {} bash -c \"echo ''; echo ''; echo '$cyn## {}$white'; echo ''; fstar.exe --record_hints --use_hints {}\""

