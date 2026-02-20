/** Click link, expect alert "You clicked it!  That's some fancy shooting!" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Alert/main');
  const dialogPromise = page.waitForEvent('dialog');
  await page.click('xpath=/html/body/a');
  const dialog = await dialogPromise;
  if (dialog.message() !== "You clicked it!  That's some fancy shooting!") {
    throw new Error(`Expected alert "You clicked it!  That's some fancy shooting!", got: ${dialog.message()}`);
  }
  await dialog.accept();
};
