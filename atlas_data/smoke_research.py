"""Browser-check the separate research area; no live Coq or model calls.

Defaults to an isolated local server. --site can check a deployed revision.
Screenshots and the result summary go to a fresh temporary directory.
"""
import argparse
from functools import partial
import hashlib
from http.server import ThreadingHTTPServer
import json
from pathlib import Path
import tempfile
import threading

from playwright.sync_api import sync_playwright, expect
from smoke_reading import QuietHandler

ROOT = Path(__file__).resolve().parent.parent


def check(site, artifacts):
    checks, errors, external = [], [], []
    with sync_playwright() as p:
        browser = p.chromium.launch()
        context = browser.new_context(viewport={"width": 1440, "height": 1050}, accept_downloads=True)
        page = context.new_page()
        page.on("pageerror", lambda error: errors.append(str(error)))

        def network(route):
            if route.request.url.startswith(site + "/") or route.request.url.startswith("blob:"):
                route.continue_()
            else:
                external.append(route.request.url)
                route.abort()

        context.route("**/*", network)
        page.goto(site + "/#/research")
        expect(page.get_by_role("heading", name="Montague, from source to proof.")).to_be_visible()
        expect(page.locator('#nav a[data-r="research"]')).to_have_attribute("aria-current", "page")
        assert page.locator('.research-files a').count() == 53
        assert page.locator('.research-page a[href^="#/edit/"]').count() == 0
        page.screenshot(path=str(artifacts / "research-desktop.png"), full_page=True)
        checks.append("Research section, three packages and 53 source links")
        page.locator('.research-page .entry-card').nth(2).click()
        expect(page.locator('.reader-selection h2')).to_have_text("temperature_countermodel")
        expect(page.locator('.research-notice')).to_contain_text("not enabled")
        assert page.locator('a[href^="#/edit/"]').count() == 0
        page.locator("#proof-search").fill("temperature_countermodel")
        expect(page.locator('#proof-outline a:visible')).to_have_count(1)
        page.screenshot(path=str(artifacts / "research-proof-desktop.png"), full_page=True)
        with page.expect_download() as info:
            page.get_by_role("button", name="Download .v", exact=True).click()
        download = info.value
        downloaded = Path(download.path()).read_bytes()
        expected = (ROOT / "deep/montague_ptq/Examples.v").read_bytes()
        assert downloaded == expected
        checks.append("Exact theorem navigation, outline search and byte-identical source download")
        page.goto(site + "/#/research-proof/__proto__")
        assert page.locator('.reader-codebar').count() == 0
        page.goto(site + "/#/proof/atlas__ttr_model")
        expect(page.get_by_role("link", name="Edit and run in Coq")).to_be_visible()
        checks.append("Unknown research routes rejected; existing atlas edit link retained")
        page.set_viewport_size({"width": 390, "height": 844})
        page.goto(site + "/#/research")
        expect(page.get_by_role("heading", name="Montague, from source to proof.")).to_be_visible()
        assert page.evaluate("document.documentElement.scrollWidth <= innerWidth + 1")
        page.screenshot(path=str(artifacts / "research-mobile.png"), full_page=True)
        page.locator('.research-page .entry-card').first.click()
        expect(page.locator('.reader-selection h2')).to_have_text("translation_interpretation")
        assert page.evaluate("document.documentElement.scrollWidth <= innerWidth + 1")
        page.screenshot(path=str(artifacts / "research-proof-mobile.png"), full_page=True)
        checks.append("Mobile research and proof views fit the viewport")
        assert not errors, errors
        revision = page.evaluate("D.revision")
        context.close()
        browser.close()
    result = {"site": site, "revision": revision, "checks": checks, "page_errors": errors,
              "blocked_external_requests": external, "paid_model_calls": 0, "coq_requests": 0,
              "download_sha256": hashlib.sha256(downloaded).hexdigest()}
    (artifacts / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print("Artifacts:", artifacts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site")
    args = parser.parse_args()
    artifacts = Path(tempfile.mkdtemp(prefix="atlas-research-browser-"))
    if args.site:
        check(args.site.rstrip("/"), artifacts)
        return
    handler = partial(QuietHandler, directory=str(ROOT / "atlas_data/site"))
    server = ThreadingHTTPServer(("127.0.0.1", 0), handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        check(f"http://127.0.0.1:{server.server_port}", artifacts)
    finally:
        server.shutdown()
        server.server_close()
        thread.join()


if __name__ == "__main__":
    main()
