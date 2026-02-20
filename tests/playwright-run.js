#!/usr/bin/env node
/**
 * Run an interactive Playwright test module.
 * Usage: node playwright-run.js <testname> [baseUrl]
 * Test modules live in playwright-tests/<testname>.js and export: async (page, baseUrl) => void
 */
const { chromium } = require('playwright');

const testName = process.argv[2];
const baseUrl = process.argv[3] || `http://localhost:${process.env.PORT || 8080}`;

if (!testName) {
  console.error('Usage: playwright-run.js <testname> [baseUrl]');
  process.exit(2);
}

const path = require('path');
const testPath = path.join(__dirname, 'playwright-tests', testName + '.js');

let test;
try {
  test = require(testPath);
} catch (e) {
  if (e.code === 'MODULE_NOT_FOUND') {
    console.error(`Test module not found: ${testPath}`);
    process.exit(2);
  }
  throw e;
}

(async () => {
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    await test(page, baseUrl.replace(/\/$/, ''));
  } finally {
    await browser.close();
  }
})().catch((err) => {
  console.error(err.message || err);
  process.exit(1);
});
