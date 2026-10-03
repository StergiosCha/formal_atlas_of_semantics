"""Run on the dedicated VM as root. Pins the final image and tests log privacy."""
from pathlib import Path
import subprocess
import time

old='sha256:92af29f43f427775b139746f1a7cb56596cd38fc21a6981efdc58b536b5d74eb'
new='sha256:31a276f63ef8bb9c21d9d739632e38559a64a379f2960bcf7606b20301ddf8b6'
for name in ['/usr/local/sbin/atlas-pull','/etc/systemd/system/atlas-coq.service']:
    path=Path(name)
    content=path.read_text().replace(old,new)
    assert new in content
    path.write_text(content)

config=Path('/etc/caddy/Caddyfile')
previous=config.read_text()
if 'request>headers delete' not in previous:
    config.write_text('''{
    log default {
        format filter {
            fields {
                request>headers delete
                resp_headers delete
            }
            wrap json
        }
    }
}
'''+previous)
try:
    subprocess.run(['caddy','validate','--config',str(config)],check=True)
except Exception:
    config.write_text(previous)
    raise
subprocess.run(['systemctl','restart','caddy'],check=True)
subprocess.run(['systemctl','daemon-reload'],check=True)
subprocess.run(['systemctl','stop','atlas-coq'],check=True)
try:
    domain='formal-atlas-coq-crete.westus2.cloudapp.azure.com'
    canary='sk-or-log-redaction-canary-20261002'
    response=subprocess.run(['curl','-sS','--resolve',domain+':443:127.0.0.1',
        '-H','X-OpenRouter-Key: '+canary,'-o','/dev/null','-w','%{http_code}',
        'https://'+domain+'/__atlas_credential_log_probe'],capture_output=True,text=True,check=True)
    assert response.stdout=='502',response.stdout
    for _ in range(20):
        logs=subprocess.run(['journalctl','-u','caddy','--since','2 minutes ago','-o','cat','--no-pager'],capture_output=True,text=True,check=True).stdout
        if '__atlas_credential_log_probe' in logs:
            break
        time.sleep(.1)
    assert '__atlas_credential_log_probe' in logs,'Expected proxy error was not logged'
    assert canary not in logs,'Dummy key leaked into proxy logs'
    print('Proxy error-path header redaction passed with a dummy key')
finally:
    subprocess.run(['systemctl','start','atlas-coq'],check=True)
print('Final pinned Coq worker activated')
