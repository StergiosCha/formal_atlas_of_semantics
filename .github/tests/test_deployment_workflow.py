"""Static safety checks for verification-gated, serialized deployment."""
from pathlib import Path
import unittest
import yaml

ROOT = Path(__file__).resolve().parents[2]
DEPLOY = yaml.safe_load((ROOT / ".github/workflows/azure-static-web-apps-orange-beach-0c447e210.yml").read_text())
VERIFY = yaml.safe_load((ROOT / ".github/workflows/verify.yml").read_text())


class DeploymentWorkflowTests(unittest.TestCase):
    def test_deployment_requires_both_check_jobs(self):
        jobs = DEPLOY["jobs"]
        self.assertEqual(set(jobs["build_and_deploy_job"]["needs"]), {"verify", "reporting"})
        self.assertEqual(jobs["verify"]["uses"], "./.github/workflows/verify.yml")
        self.assertNotIn("always()", jobs["build_and_deploy_job"]["if"])
        self.assertNotIn("secrets", jobs["verify"])
        self.assertEqual(set(VERIFY.get("on", VERIFY.get(True))), {"workflow_call"})

    def test_target_serialization_does_not_cancel_uploads(self):
        group = DEPLOY["concurrency"]
        self.assertIs(group["cancel-in-progress"], False)
        self.assertIn("github.event.pull_request.number", group["group"])
        self.assertIn("github.ref", group["group"])

    def test_forks_are_checked_without_deployment_credentials(self):
        for job in ("build_and_deploy_job", "close_pull_request_job"):
            self.assertIn("github.event.pull_request.head.repo.full_name == github.repository", DEPLOY["jobs"][job]["if"])
        self.assertEqual(DEPLOY["permissions"], {"contents": "read"})
        self.assertNotIn("secrets", DEPLOY["jobs"]["reporting"])

    def test_only_current_verified_production_revision_is_uploaded(self):
        steps = DEPLOY["jobs"]["build_and_deploy_job"]["steps"]
        current = next(s for s in steps if s.get("id") == "current")
        self.assertIn("ref.data.object.sha === context.sha", current["with"]["script"])
        self.assertIn("heads/main", current["with"]["script"])
        upload = next(s for s in steps if s.get("name") == "Build And Deploy")
        self.assertIn("steps.current.outputs.result == 'true'", upload["if"])
        self.assertIs(upload["with"]["skip_app_build"], True)
        self.assertLess(next(i for i,s in enumerate(steps) if s.get("name") == "Build verified site"),
                        steps.index(upload))
        self.assertNotIn("ref", steps[0].get("with", {}))

    def test_reporting_checks_registry_and_all_site_routes(self):
        script = DEPLOY["jobs"]["reporting"]["steps"][-1]["run"]
        for command in ("source_registry.py", "consolidate.py", "git diff --exit-code",
                        "test_source_registry.cjs", "test_landing.cjs", "test_outcomes.cjs"):
            self.assertIn(command, script)
        self.assertNotIn("ATLAS_PAPERS", script)

    def test_citation_does_not_invent_a_release_or_doi(self):
        citation = yaml.safe_load((ROOT / "CITATION.cff").read_text())
        self.assertEqual(citation["cff-version"], "1.2.0")
        self.assertEqual(citation["type"], "software")
        self.assertNotIn("doi", citation)
        self.assertNotIn("version", citation)
        self.assertNotIn("date-released", citation)
        self.assertTrue(citation["authors"])


if __name__ == "__main__":
    unittest.main()
