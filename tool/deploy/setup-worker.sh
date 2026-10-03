#!/bin/sh
# Run as root on the approved dedicated VM, via Azure Run Command.
set -eu
export DEBIAN_FRONTEND=noninteractive
apt-get install -y debian-keyring debian-archive-keyring apt-transport-https curl gnupg
curl -fsSL https://dl.cloudsmith.io/public/caddy/stable/gpg.key | gpg --dearmor --yes -o /usr/share/keyrings/caddy-stable-archive-keyring.gpg
curl -fsSL https://dl.cloudsmith.io/public/caddy/stable/debian.deb.txt -o /etc/apt/sources.list.d/caddy-stable.list
apt-get update -qq
apt-get -o Dpkg::Options::=--force-confold install -y caddy
caddy validate --config /etc/caddy/Caddyfile
sed -i 's|formalatlasacr.azurecr.io/atlas-checker:byok-20261002|formalatlasacr.azurecr.io/atlas-checker@sha256:31a276f63ef8bb9c21d9d739632e38559a64a379f2960bcf7606b20301ddf8b6|g; s|sha256:92af29f43f427775b139746f1a7cb56596cd38fc21a6981efdc58b536b5d74eb|sha256:31a276f63ef8bb9c21d9d739632e38559a64a379f2960bcf7606b20301ddf8b6|g' /usr/local/sbin/atlas-pull /etc/systemd/system/atlas-coq.service
sed -i 's/^Requires=docker.service$/Requires=docker.service atlas-metadata-guard.service/; s/^After=docker.service network-online.target$/After=docker.service network-online.target atlas-metadata-guard.service\nPartOf=docker.service/' /etc/systemd/system/atlas-coq.service
sed -i '/^Requires=docker.service$/a PartOf=docker.service' /etc/systemd/system/atlas-metadata-guard.service
systemctl daemon-reload
systemctl enable --now caddy
systemctl restart caddy
systemctl restart --no-block atlas-coq
systemctl is-active caddy
