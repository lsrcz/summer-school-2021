#!/bin/bash
# pulled this into a separate script so we could use /etc/os-release to get release info
. /etc/os-release
wget https://packages.microsoft.com/config/${ID}/${VERSION_ID}/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
dpkg -i packages-microsoft-prod.deb
rm packages-microsoft-prod.deb
apt-get update
apt-get install -y dotnet-sdk-5.0
