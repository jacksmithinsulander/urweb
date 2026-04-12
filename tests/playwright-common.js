#!/usr/bin/env node

function stripFirstPathSegment(rawUrl) {
  const url = new URL(rawUrl);
  const parts = url.pathname.split('/').filter(Boolean);
  if (parts.length < 2) {
    return null;
  }
  url.pathname = '/' + parts.slice(1).join('/');
  return url.toString();
}

async function gotoResolved(page, rawUrl, options) {
  let response = await page.goto(rawUrl, options);
  let finalUrl = rawUrl;

  if (response && response.status() === 404) {
    const altUrl = stripFirstPathSegment(rawUrl);
    if (altUrl && altUrl !== rawUrl) {
      const altResponse = await page.goto(altUrl, options);
      if (!altResponse || altResponse.status() !== 404) {
        response = altResponse;
        finalUrl = altUrl;
      }
    }
  }

  return { response, url: finalUrl };
}

function patchPageGoto(page) {
  const originalGoto = page.goto.bind(page);
  page.goto = async (rawUrl, options) => {
    let response = await originalGoto(rawUrl, options);

    if (response && response.status() === 404) {
      const altUrl = stripFirstPathSegment(rawUrl);
      if (altUrl && altUrl !== rawUrl) {
        const altResponse = await originalGoto(altUrl, options);
        if (!altResponse || altResponse.status() !== 404) {
          return altResponse;
        }
      }
    }

    return response;
  };
}

module.exports = { gotoResolved, patchPageGoto };
