#!/usr/bin/env bash

sudo apt update && sudo apt upgrade -y
sudo apt install -y curl git fish vim


# Install Lean 4
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
echo "source $HOME/.elan/env" >> $HOME/.config/fish/config.fish
source $HOME/.elan/env
lean --version
