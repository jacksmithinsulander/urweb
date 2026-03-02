/** Click goofy element (name=beppo, data-role=excellence), expect alert */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/main');
  let dialogMsg = null;
  page.once('dialog', async dialog => {
    dialogMsg = dialog.message();
    await dialog.accept();
  });
  await page.click('[name="beppo"][data-role="excellence"]');
  if (dialogMsg !== "You clicked it!  That's some fancy shooting!") {
    throw new Error(`Expected "You clicked it!  That's some fancy shooting!", got: ${dialogMsg}`);
  }
};
