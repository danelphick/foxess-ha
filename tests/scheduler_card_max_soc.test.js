import { describe, it, expect, vi, beforeAll, afterEach } from 'vitest';

beforeAll(async () => {
  await import('../custom_components/foxess/scheduler_card.js');
});

afterEach(() => {
  document.body.innerHTML = '';
});

const DEVICE_SN = 'SN123456';

function makeGroup(extraParam) {
  return {
    startHour: 6, startMinute: 0,
    endHour: 12, endMinute: 0,
    enable: 1,
    workMode: 'ForceCharge',
    extraParam,
  };
}

function makeHass(groups = [], sendOverride = null) {
  const send = sendOverride ?? vi.fn().mockImplementation(msg => {
    if (msg.type === 'foxess/get_templates') return Promise.resolve({ templates: [] });
    return Promise.resolve({ ok: true });
  });
  return {
    states: {
      'sensor.foxess_scheduler_enabled': {
        state: 'enabled',
        attributes: { friendly_name: 'FoxESS Scheduler Enabled' },
      },
      'sensor.foxess_scheduler_groups': {
        state: String(groups.length),
        attributes: { groups, device_sn: DEVICE_SN },
      },
    },
    connection: { sendMessagePromise: send },
  };
}

function mountCard(hass) {
  const Card = customElements.get('foxess-scheduler-card');
  const card = new Card();
  document.body.appendChild(card);
  card.hass = hass;
  return card;
}

async function tick() {
  await new Promise(resolve => setTimeout(resolve, 0));
}

// ---------------------------------------------------------------------------
// Main card table
// ---------------------------------------------------------------------------

describe('Max SoC - main card table', () => {
  it('has "Max SoC" column header after "FD Power"', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 80 })]));
    const headers = Array.from(card.shadowRoot.querySelectorAll('table thead th')).map(th => th.textContent.trim());
    const fdPowerIdx = headers.indexOf('FD Power');
    const maxSocIdx = headers.indexOf('Max SoC');
    expect(maxSocIdx).toBeGreaterThan(-1);
    expect(maxSocIdx).toBe(fdPowerIdx + 1);
  });

  it('renders maxSoc value from extraParam', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 75 })]));
    const cells = Array.from(card.shadowRoot.querySelectorAll('table tbody td'));
    expect(cells.some(td => td.textContent.trim() === '75%')).toBe(true);
  });

  it('defaults maxSoc to 100 when extraParam.maxSoc is absent', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000 })]));
    const cells = Array.from(card.shadowRoot.querySelectorAll('table tbody td'));
    expect(cells.some(td => td.textContent.trim() === '100%')).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// Edit modal
// ---------------------------------------------------------------------------

describe('Max SoC - edit modal', () => {
  it('has "Max SoC%" column header after "FD Pwr (W)"', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 80 })]));
    card.shadowRoot.querySelector('.edit-btn').click();
    const headers = Array.from(card.shadowRoot.querySelectorAll('.modal-table thead th')).map(th => th.textContent.trim());
    const fdPwrIdx = headers.indexOf('FD Pwr (W)');
    const maxSocIdx = headers.indexOf('Max SoC%');
    expect(maxSocIdx).toBeGreaterThan(-1);
    expect(maxSocIdx).toBe(fdPwrIdx + 1);
  });

  it('renders maxSoc input with the value from group data', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 75 })]));
    card.shadowRoot.querySelector('.edit-btn').click();
    const input = card.shadowRoot.querySelector('.num-input[data-field="maxSoc"]');
    expect(input).not.toBeNull();
    expect(input.value).toBe('75');
  });

  it('maxSoc input appears after fdPwr input in the DOM', () => {
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 80 })]));
    card.shadowRoot.querySelector('.edit-btn').click();
    const inputs = Array.from(card.shadowRoot.querySelectorAll('.num-input'));
    const fdPwrIdx = inputs.findIndex(i => i.dataset.field === 'fdPwr');
    const maxSocIdx = inputs.findIndex(i => i.dataset.field === 'maxSoc');
    expect(maxSocIdx).toBeGreaterThan(fdPwrIdx);
  });
});

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

describe('Max SoC - validation', () => {
  it('blocks save and shows error when maxSoc <= fdSoc', () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 90, fdPwr: 0, maxSoc: 80 })], send));
    card.shadowRoot.querySelector('.edit-btn').click();
    card.shadowRoot.querySelector('.save-btn').click();
    expect(card.shadowRoot.querySelector('.modal-error').textContent).toBeTruthy();
    expect(send).not.toHaveBeenCalledWith(expect.objectContaining({ type: 'foxess/save_schedule' }));
  });

  it('blocks save and shows error when fdSoc <= minSocOnGrid', () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 50, fdSoc: 30, fdPwr: 0, maxSoc: 100 })], send));
    card.shadowRoot.querySelector('.edit-btn').click();
    card.shadowRoot.querySelector('.save-btn').click();
    expect(card.shadowRoot.querySelector('.modal-error').textContent).toBeTruthy();
    expect(send).not.toHaveBeenCalledWith(expect.objectContaining({ type: 'foxess/save_schedule' }));
  });

  it('allows save to proceed when maxSoc > fdSoc > minSocOnGrid', async () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 0, maxSoc: 90 })], send));
    card.shadowRoot.querySelector('.edit-btn').click();
    card.shadowRoot.querySelector('.save-btn').click();
    await tick();
    expect(send).toHaveBeenCalledWith(expect.objectContaining({ type: 'foxess/save_schedule' }));
    expect(card.shadowRoot.querySelector('.modal-error').textContent).toBe('');
  });
});

// ---------------------------------------------------------------------------
// Save payload
// ---------------------------------------------------------------------------

describe('Max SoC - save payload', () => {
  it('includes maxSoc in extraParam when saving', async () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass([makeGroup({ minSocOnGrid: 10, fdSoc: 50, fdPwr: 2000, maxSoc: 80 })], send));
    card.shadowRoot.querySelector('.edit-btn').click();
    card.shadowRoot.querySelector('.save-btn').click();
    await tick();
    expect(send).toHaveBeenCalledWith(
      expect.objectContaining({
        type: 'foxess/save_schedule',
        groups: expect.arrayContaining([
          expect.objectContaining({
            extraParam: expect.objectContaining({ maxSoc: 80 }),
          }),
        ]),
      })
    );
  });

});
