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
# Fresh provisioning uses the pinned image in cloud-init.yaml. Existing workers
# must use a release-specific activator with health checks and rollback instead.
sed -i 's/^Requires=docker.service$/Requires=docker.service atlas-metadata-guard.service/; s/^After=docker.service network-online.target$/After=docker.service network-online.target atlas-metadata-guard.service\nPartOf=docker.service/' /etc/systemd/system/atlas-coq.service
sed -i '/^Requires=docker.service$/a PartOf=docker.service' /etc/systemd/system/atlas-metadata-guard.service
systemctl daemon-reload
systemctl enable --now caddy
systemctl restart caddy
systemctl restart --no-block atlas-coq
systemctl is-active caddy
