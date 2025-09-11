#!/usr/bin/env bash
if [[ "" == Username* ]]; then
  echo "x-access-token"
elif [[ "" == Password* ]]; then
  cat "../../internal/keys/admin_token.txt"
else
  echo ""
fi
