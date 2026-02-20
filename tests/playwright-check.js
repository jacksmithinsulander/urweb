#!/usr/bin/env node
/**
 * Playwright-based DOM check for Ur/Web tests.
 * Usage: node playwright-check.js <url> <xpath> [expected_text]
 * Exits 0 if XPath matches at least one element (and optional text matches).
 */
const { chromium } = require('playwright');

(async () => {
  const [url, xpath, expectedText] = process.argv.slice(2);
  if (!url || !xpath) {
    console.error('Usage: playwright-check.js <url> <xpath> [expected_text]');
    process.exit(2);
  }

  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    await page.goto(url, { waitUntil: 'domcontentloaded', timeout: 10000 });
    const loc = page.locator(`xpath=${xpath}`);
    const count = await loc.count();
    if (count === 0) {
      console.error(`XPath matched no elements: ${xpath}`);
      process.exit(1);
    }
    if (expectedText) {
      const text = await loc.first().textContent();
      if (!text || !text.includes(expectedText)) {
        console.error(`Expected text containing "${expectedText}", got: ${JSON.stringify(text)}`);
        process.exit(1);
      }
    }
    process.exit(0);
  } finally {
    await browser.close();
  }
})().catch((err) => {
  console.error(err.message || err);
  process.exit(1);
});
